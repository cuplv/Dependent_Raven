//! backend/src/model/name.rs
//! [KOR] 모델의 원소에 소스 어휘의 이름을 붙입니다. 영-인자 생성자의 상수가 가리키는
//!       원소는 그 생성자 이름을, 생성자 관계의 튜플로 만들어지는 원소는
//!       `C(인자 이름들)`을 받으며(고정점까지 반복), 어떤 생성자도 만들지 않는
//!       원소는 정크(junk)로 `sort!k` 태그를 받습니다.
//! [ENG] Gives the model's elements names in the source vocabulary. The element
//!       a nullary constructor's constant denotes gets that constructor's name;
//!       an element some constructor tuple produces from already-named
//!       arguments gets `C(args)`, repeated to a fixed point; whatever is left
//!       is junk -- no constructor produces it, which the partial semantics
//!       allows and a total model never contains -- and gets a `sort!k` tag.
//!       All SMT names are derived from `Program.datatypes` through the
//!       backend's own naming scheme, so this works for any program.

use super::{Elem, Model};
use crate::smt::builder::{render_sort, sanitize_id};
use frontend::ast::{BaseType, Program};
use std::collections::BTreeMap;

/// [ENG] Source-level names for a model's elements.
#[derive(Debug, Default)]
pub struct Names {
    /// element tag -> its name (`Z`, `S(S(Z))`, `nat!3`, `true`)
    pub of_elem: BTreeMap<Elem, String>,
    /// the junk elements, by sort name in the source (`Nat`), with their tags
    pub junk: Vec<(String, String)>,
}

impl Names {
    /// [ENG] The name of an element; Bool literals name themselves.
    pub fn get(&self, elem: &Elem) -> String {
        self.of_elem.get(elem).cloned().unwrap_or_else(|| elem.clone())
    }
}

/// [ENG] CamlStar's display rule, exactly: a nullary constructor's element is
///       written with the constructor's name, every other element of a datatype
///       universe as `Sort!k` with the solver's index. (No constructor-term
///       naming, no junk classification: `name_elements` does those.)
pub fn tags_only(model: &Model, program: &Program) -> Names {
    let mut names = Names::default();
    names.of_elem.insert("true".to_string(), "true".to_string());
    names.of_elem.insert("false".to_string(), "false".to_string());
    for (enum_name, variants) in &program.datatypes {
        for (variant, fields) in variants {
            if fields.is_empty() {
                let constant = sanitize_id(&format!("{}::{}", enum_name, variant));
                if let Some(elem) = model.consts.get(&constant) {
                    names.of_elem.entry(elem.clone()).or_insert_with(|| variant.clone());
                }
            }
        }
        let sort = render_sort(&BaseType::Custom(enum_name.clone()));
        if let Some(universe) = model.universes.get(&sort) {
            for (k, elem) in universe.iter().enumerate() {
                names
                    .of_elem
                    .entry(elem.clone())
                    .or_insert_with(|| format!("{}!{}", enum_name, tag_index(elem).unwrap_or(k)));
            }
        }
    }
    names
}

pub fn name_elements(model: &Model, program: &Program) -> Names {
    let mut names = Names::default();
    names.of_elem.insert("true".to_string(), "true".to_string());
    names.of_elem.insert("false".to_string(), "false".to_string());

    // 1. Nullary constructors: their constants pick out elements directly.
    for (enum_name, variants) in &program.datatypes {
        for (variant, fields) in variants {
            if fields.is_empty() {
                let constant = sanitize_id(&format!("{}::{}", enum_name, variant));
                if let Some(elem) = model.consts.get(&constant) {
                    names.of_elem.entry(elem.clone()).or_insert_with(|| variant.clone());
                }
            }
        }
    }

    // 2. Constructor tuples over named arguments, to a fixed point.
    loop {
        let mut progressed = false;
        for (enum_name, variants) in &program.datatypes {
            for (variant, fields) in variants {
                if fields.is_empty() {
                    continue;
                }
                let relation = sanitize_id(&format!("{}::{}_rel", enum_name, variant));
                let Some(table) = model.rels.get(&relation) else { continue };
                for (tuple, value) in &table.entries {
                    if value != "true" {
                        continue;
                    }
                    let (result, args) = tuple.split_last().expect("a constructor relation has a result column");
                    if names.of_elem.contains_key(result) {
                        continue;
                    }
                    let arg_names: Option<Vec<&String>> = args.iter().map(|a| names.of_elem.get(a)).collect();
                    if let Some(arg_names) = arg_names {
                        let rendered = format!(
                            "{}({})",
                            variant,
                            arg_names.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
                        );
                        names.of_elem.insert(result.clone(), rendered);
                        progressed = true;
                    }
                }
            }
        }
        if !progressed {
            break;
        }
    }

    // 3. Junk: elements of a datatype's universe that no constructor produced.
    for (enum_name, _) in &program.datatypes {
        let sort = render_sort(&BaseType::Custom(enum_name.clone()));
        let Some(universe) = model.universes.get(&sort) else { continue };
        for (k, elem) in universe.iter().enumerate() {
            if !names.of_elem.contains_key(elem) {
                let tag = format!("{}!{}", enum_name.to_lowercase(), tag_index(elem).unwrap_or(k));
                names.of_elem.insert(elem.clone(), tag.clone());
                names.junk.push((enum_name.clone(), tag));
            }
        }
    }
    // `Program.datatypes` is a HashMap; keep the report deterministic.
    names.junk.sort();
    names
}

/// [ENG] The index a solver put in an element tag (`UI_Nat!val!3` -> 3), if any.
fn tag_index(elem: &Elem) -> Option<usize> {
    elem.rsplit('!').next()?.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Table;
    use std::collections::HashMap;

    // A program of the test's own making, referred to only through the names it
    // registers; the SMT names are derived with the backend's scheme.
    fn program() -> Program {
        let mut program = Program { datatypes: HashMap::new(), functions: HashMap::new(), goals: Vec::new() };
        frontend::api::register_enum(&mut program, "Peano", "enum Peano { Zero, Succ(Box<Peano>) }");
        frontend::api::register_enum(&mut program, "Cell", "enum Cell { Mk(Peano, bool) }");
        program
    }

    #[test]
    fn constructors_name_elements_and_the_rest_is_junk() {
        let p = program();
        let peano = render_sort(&BaseType::Custom("Peano".into()));
        let cell = render_sort(&BaseType::Custom("Cell".into()));
        let e: Vec<Elem> = (0..4).map(|k| format!("{}!val!{}", peano, k)).collect();
        let c: Vec<Elem> = (0..2).map(|k| format!("{}!val!{}", cell, k)).collect();

        let mut m = Model::default();
        m.universes.insert(peano.clone(), e.clone());
        m.universes.insert(cell.clone(), c.clone());
        m.consts.insert(sanitize_id("Peano::Zero"), e[0].clone());
        m.rels.insert(
            sanitize_id("Peano::Succ_rel"),
            Table {
                entries: vec![(vec![e[0].clone(), e[1].clone()], "true".into()), (vec![e[1].clone(), e[2].clone()], "true".into())],
                else_value: Some("false".into()),
            },
        );
        m.rels.insert(
            sanitize_id("Cell::Mk_rel"),
            Table { entries: vec![(vec![e[2].clone(), "true".into(), c[0].clone()], "true".into())], else_value: Some("false".into()) },
        );

        let n = name_elements(&m, &p);
        assert_eq!(n.get(&e[0]), "Zero");
        assert_eq!(n.get(&e[1]), "Succ(Zero)");
        assert_eq!(n.get(&e[2]), "Succ(Succ(Zero))");
        assert_eq!(n.get(&e[3]), "peano!3");
        assert_eq!(n.get(&c[0]), "Mk(Succ(Succ(Zero)), true)");
        assert_eq!(n.get(&c[1]), "cell!1");
        assert_eq!(n.junk, vec![("Cell".to_string(), "cell!1".to_string()), ("Peano".to_string(), "peano!3".to_string())]);
    }
}
