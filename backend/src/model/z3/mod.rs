//! backend/src/model/z3/mod.rs
//! [ENG] Finds a model for a query with the z3 API (the route CamlStar takes with
//!       the OCaml bindings) and converts it to the solver-independent `Model`.
//!       Everything z3-specific lives in this directory.

use super::{declared_relations, Elem, Model, Table};
use crate::smt::solver::Verdict;
use std::collections::BTreeMap;
use z3::ast::{Ast, Bool, Dynamic};
use z3::{with_z3_config, Config, SatResult, Solver};

/// [ENG] A relation's table is enumerated only when the product of its column
///       universes is at most this many tuples; wider relations over larger
///       universes are left without a table (`else_value: None`) rather than
///       spending minutes on them.
const MAX_TUPLES_PER_RELATION: usize = 200_000;

/// [ENG] Solves a query in-process with z3, with no time limit, and returns the
///       verdict together with the model of the same run when it is `sat`.
///       Anything that is not a definite `sat`/`unsat` -- z3's own `unknown`,
///       or an error such as running out of memory, which the crate raises as
///       a panic -- is reported as `Unknown`. The z3 crate (0.21) keeps one
///       context per thread, configured for the duration of the closure; the
///       whole solve and extraction happens inside it.
pub fn solve(query: &str) -> (Verdict, Option<Model>) {
    let query = query.to_string();
    let outcome = std::panic::catch_unwind(move || {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);
        with_z3_config(&cfg, move || {
            let solver = Solver::new();
            solver.from_string(query.clone());
            match solver.check() {
                SatResult::Unsat => (Verdict::Unsat, None),
                SatResult::Unknown => (Verdict::Unknown, None),
                SatResult::Sat => (Verdict::Sat, extract(&solver, &query)),
            }
        })
    });
    match outcome {
        Ok(result) => result,
        Err(_) => (Verdict::Unknown, None), // z3 raised an error (e.g. out of memory)
    }
}

/// [ENG] Runs z3 on the SMT-LIB text of a query for at most `limit_ms` and
///       returns its model if the query is satisfiable within the limit. For
///       experiments on saved query files; the driver uses `solve`.
pub fn find_model(query: &str, limit_ms: u64) -> Option<Model> {
    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    cfg.set_timeout_msec(limit_ms);
    let query = query.to_string();
    with_z3_config(&cfg, move || {
        let solver = Solver::new();
        solver.from_string(query.clone());
        if solver.check() != SatResult::Sat {
            return None;
        }
        extract(&solver, &query)
    })
}

/// [ENG] The model of a solver that has just answered `sat`, converted to the
///       solver-independent `Model`: universes, constants, and every declared
///       relation's table, the latter by evaluating the relation on each tuple
///       of its column universes (z3 reports interpretations as formulas, not
///       as tables; CamlStar enumerates for the same reason).
fn extract(solver: &Solver, query: &str) -> Option<Model> {
    let signatures = declared_relations(query);
    {
        let model = solver.get_model()?;

        // Universes, keeping each element's AST so relations can be applied to it.
        let mut out = Model::default();
        let mut elements: BTreeMap<String, Vec<(Elem, Dynamic)>> = BTreeMap::new();
        for (sort, universe) in model.sort_universes() {
            let elems: Vec<(Elem, Dynamic)> = (0..universe.len())
                .map(|i| {
                    let ast = universe.get(i);
                    (elem_of(&ast.to_string()), ast)
                })
                .collect();
            out.universes.insert(sort.to_string(), elems.iter().map(|(e, _)| e.clone()).collect());
            elements.insert(sort.to_string(), elems);
        }
        let booleans: Vec<(Elem, Dynamic)> = [true, false]
            .iter()
            .map(|b| (b.to_string(), Dynamic::from_ast(&Bool::from_bool(*b))))
            .collect();

        for decl in model.iter() {
            if decl.arity() == 0 {
                let value = model.eval(&decl.apply(&[]), true)?;
                out.consts.insert(decl.name(), elem_of(&value.to_string()));
                continue;
            }
            // A relation. z3 reports its interpretation as a formula over the
            // arguments, not as a table, so (as CamlStar does) the table is
            // built by evaluating the relation on every tuple of its column
            // universes. The column sorts come from the query's own
            // declaration of the relation.
            let Some((_, columns)) = signatures.iter().find(|(n, _)| *n == decl.name()) else { continue };
            let column_elems: Option<Vec<&Vec<(Elem, Dynamic)>>> = columns
                .iter()
                .map(|sort| match sort.as_str() {
                    "Bool" => Some(&booleans),
                    other => elements.get(other),
                })
                .collect();
            // A column of a sort with no universe (e.g. Unit) makes the relation uninformative.
            let Some(column_elems) = column_elems else { continue };
            let size: usize = column_elems.iter().map(|u| u.len()).product();
            if size > MAX_TUPLES_PER_RELATION {
                out.rels.insert(decl.name(), Table { entries: Vec::new(), else_value: None });
                continue;
            }
            let mut entries = Vec::new();
            for tuple in cartesian(&column_elems) {
                let args: Vec<&dyn Ast> = tuple.iter().map(|(_, ast)| ast as &dyn Ast).collect();
                let Some(value) = model.eval(&decl.apply(&args), true) else { continue };
                if value.to_string() == "true" {
                    entries.push((tuple.iter().map(|(e, _)| e.clone()).collect(), "true".to_string()));
                }
            }
            out.rels.insert(decl.name(), Table { entries, else_value: Some("false".to_string()) });
        }
        Some(out)
    }
}

/// [ENG] Every choice of one element per column, in column-major order.
fn cartesian<'a>(columns: &[&'a Vec<(Elem, Dynamic)>]) -> Vec<Vec<&'a (Elem, Dynamic)>> {
    columns.iter().fold(vec![Vec::new()], |acc, column| {
        acc.iter()
            .flat_map(|prefix| column.iter().map(move |e| {
                let mut next = prefix.clone();
                next.push(e);
                next
            }))
            .collect()
    })
}

/// [ENG] z3 prints an element of an uninterpreted sort as `UI_Nat!val!2`; that
///       tag is the element's identity for the rest of the module.
fn elem_of(printed: &str) -> Elem {
    printed.trim().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Step-0 smoke test: the crate links against the installed libz3, parses
    // SMT-LIB text, and hands back a model with the constant's element.
    #[test]
    fn links_parses_and_reads_a_constant() {
        let q = "(declare-sort S 0)(declare-const a S)(declare-const b S)(assert (distinct a b))(check-sat)";
        let m = find_model(q, 5_000).expect("satisfiable");
        assert_eq!(m.consts.len(), 2, "{:?}", m.consts);
        assert_ne!(m.consts["a"], m.consts["b"]);
    }

    // Any satisfiable query the tool produced (the newest `*_failed_query.smt2`
    // in test_suite/logs, whatever program it came from) yields a well-formed
    // model. Nothing here depends on the program's type or function names:
    // the properties checked hold for every relational-abstraction query.
    #[test]
    fn real_query_gives_a_well_formed_model() {
        let logs = concat!(env!("CARGO_MANIFEST_DIR"), "/../test_suite/logs");
        let Ok(dir) = std::fs::read_dir(logs) else { return };
        let mut queries: Vec<_> = dir
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.to_string_lossy().ends_with("_failed_query.smt2"))
            .collect();
        queries.sort();
        let Some(path) = queries.last() else { return };
        let q = std::fs::read_to_string(path).unwrap();
        let Some(m) = find_model(&q, 10_000) else { return }; // an UNKNOWN goal's query may be unsat or slow

        let known = |e: &Elem| e == "true" || e == "false" || m.universes.values().any(|u| u.contains(e));
        assert!(!m.universes.is_empty(), "no uninterpreted sort in {:?}", path);
        for (name, elem) in &m.consts {
            assert!(known(elem), "constant {} has an element outside every universe: {}", name, elem);
        }
        for (name, table) in &m.rels {
            for (args, value) in &table.entries {
                assert!(args.iter().all(known), "{}: unknown element in {:?}", name, args);
                assert!(known(value), "{}: unknown value {}", name, value);
            }
            // Every relation the encoding declares carries a functionality axiom:
            // among the tuples where it holds, the inputs determine the output.
            let holds: Vec<&Vec<Elem>> = table.entries.iter().filter(|(_, v)| v == "true").map(|(a, _)| a).collect();
            let inputs: std::collections::BTreeSet<&[Elem]> =
                holds.iter().map(|a| &a[..a.len() - 1]).collect();
            assert_eq!(inputs.len(), holds.len(), "{} is not functional: {:?}", name, holds);
        }
        assert!(
            m.rels.values().any(|t| t.entries.iter().any(|(_, v)| v == "true")),
            "no relation holds anywhere; the ledger's witnesses should force some tuples"
        );
    }

    #[test]
    fn unsat_gives_no_model() {
        let q = "(declare-const p Bool)(assert p)(assert (not p))(check-sat)";
        assert!(find_model(q, 5_000).is_none());
    }
}
