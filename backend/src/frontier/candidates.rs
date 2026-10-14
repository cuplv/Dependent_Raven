//! [KOR] 한 라운드: 장부(goal·가설·패턴·힌트가 이미 이름 붙인 적용 항)의 각 항을 한
//!       단계 전개하고, 전개가 필요로 하지만 질의에 없는 적용 항을 후보로 모읍니다.
//!       후보는 (a) 아직 없고, (b) goal의 바인더만으로 쓸 수 있고, (c) 적용 항입니다:
//!       우변 전체(깊은 힌트 하나)와 가드의 적용 항. 가드 없는 생성자 결과는 파생
//!       모양으로 기록됩니다.
//! [ENG] One round: unfold every application the ledger already names (goal,
//!       hypotheses, patterns, hints) one step and collect the applications those
//!       unfoldings need but the query lacks. A candidate must be (a) not present
//!       yet, (b) writable from the goal's binders, (c) an application: the rhs as
//!       a whole (one deep hint) and the guards' applications. An unguarded
//!       constructor result is recorded as a derived shape.

use std::collections::HashSet;

use frontend::ast::{Expr, Goal, Ident};
use frontend::auto_inst::collect_ground_terms;

use crate::cex::dissect::{dissect, VcParts};
use crate::cex::print::print_term;
use crate::frontier::shape::{goal_atoms, Shapes};
use crate::frontier::unroll::unroll;
use crate::smt::DefEq;

/// [ENG] The result of one round. `added` is empty exactly when the round
///       saturated: nothing left to instantiate. `stuck` lists the ledger
///       applications of bodied functions that matched no equation — the ones
///       whose scrutinee argument has no known shape — for the report.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct Round {
    pub added: Vec<Expr>,
    pub stuck: Vec<Expr>,
}

/// [KOR] 장부: goal의 전건·핵심, 가설(게이트 포함), 경로 조건, 힌트에 나타나는 모든
///       적용 항, 안쪽 먼저, 중복 없이.
/// [ENG] The ledger: every application in the goal's assumptions and core, the
///       hypotheses (gates included), the path conditions and the hints —
///       inner-first within each piece, de-duplicated across them.
pub fn ledger(parts: &VcParts, instantiations: &[Expr]) -> Vec<Expr> {
    let mut pieces: Vec<&Expr> = Vec::new();
    pieces.extend(parts.path_conds.iter());
    for h in &parts.hypotheses {
        if let Some(g) = &h.gate {
            pieces.push(g);
        }
        pieces.push(&h.fact);
    }
    pieces.extend(goal_atoms(parts));
    pieces.extend(instantiations.iter());

    let mut out: Vec<Expr> = Vec::new();
    for piece in pieces {
        for t in collect_ground_terms(piece) {
            if !out.contains(&t) {
                out.push(t);
            }
        }
    }
    out
}

/// [ENG] The outermost application(s) of a guard: the guard call itself under a
///       `!`, or the applications on either side of an `x == e` let-equality.
fn outermost_apps(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::Call { .. } | Expr::Constructor { args: _, .. } => {
            if !matches!(e, Expr::Constructor { args, .. } if args.is_empty()) {
                out.push(e.clone());
            }
        }
        Expr::BinOp { left, right, .. } => {
            outermost_apps(left, out);
            outermost_apps(right, out);
        }
        Expr::UnOp { expr, .. } => outermost_apps(expr, out),
        Expr::If { cond, then_expr, else_expr } => {
            outermost_apps(cond, out);
            outermost_apps(then_expr, out);
            outermost_apps(else_expr, out);
        }
        _ => {}
    }
}

fn free_vars(e: &Expr, out: &mut HashSet<Ident>) {
    match e {
        Expr::Var(v) => {
            out.insert(v.clone());
        }
        Expr::Call { args, .. } | Expr::Constructor { args, .. } | Expr::Tuple(args) => {
            for a in args {
                free_vars(a, out);
            }
        }
        Expr::BinOp { left, right, .. } => {
            free_vars(left, out);
            free_vars(right, out);
        }
        Expr::UnOp { expr, .. } => free_vars(expr, out),
        Expr::If { cond, then_expr, else_expr } => {
            free_vars(cond, out);
            free_vars(then_expr, out);
            free_vars(else_expr, out);
        }
        _ => {}
    }
}

/// [ENG] Present-set keys: a term as written and as shape-expanded, so an
///       unfolding of a present term (`sorted(Cons(h2, t2))` for `sorted(t)` under
///       `t ↦ Cons(h2, t2)`) is recognised as present.
fn keys(shapes: &Shapes, t: &Expr) -> [String; 2] {
    [print_term(t), print_term(&shapes.expand(t))]
}

/// [KOR] 한 라운드. `shapes`는 라운드 안에서 파생 모양으로 자랍니다; 호출자는
///       라운드 사이에 같은 환경을 유지합니다.
/// [ENG] One round over `goal`. `shapes` grows with derived shapes during the
///       round; callers keep the same environment across rounds.
pub fn round(eqs: &[DefEq], goal: &Goal, shapes: &mut Shapes) -> Round {
    let parts = dissect(&goal.property);
    shapes.seed_from(&parts);
    let scope: HashSet<Ident> = parts.skolems.iter().map(|(n, _)| n.clone()).collect();
    let bodied: HashSet<&Ident> = eqs.iter().map(|e| &e.func).collect();
    let terms = ledger(&parts, &goal.instantiations);

    let mut present: HashSet<String> = HashSet::new();
    for t in &terms {
        for k in keys(shapes, t) {
            present.insert(k);
        }
    }

    let mut result = Round::default();
    let closed = |t: &Expr| {
        let mut fv = HashSet::new();
        free_vars(t, &mut fv);
        fv.is_subset(&scope)
    };

    for app in &terms {
        let Expr::Call { func, .. } = app else {
            continue;
        };
        if !bodied.contains(func) {
            continue;
        }
        let unfoldings = unroll(eqs, shapes, app);
        if unfoldings.is_empty() {
            result.stuck.push(app.clone());
            continue;
        }
        for u in &unfoldings {
            // [KOR] 필요한 항: 우변 전체(적용 항이면 — 깊은 힌트 하나가 그 부분항까지
            //       증인을 만듭니다)와 각 가드의 가장 바깥 적용 항. CamlStar와 같은
            //       선택: peephole이 우변의 존재를 보장하더라도 중복 증인은 건전하고,
            //       가드 아래의 결과는 그 보장을 받지 못할 수 있습니다.
            // [ENG] Needed terms: the rhs as a whole when it is an application (one
            //       deep hint materialises its subterms too) and each guard's
            //       outermost application(s). CamlStar's choice: even where the
            //       peephole asserts the result, a redundant witness is sound, and
            //       a result under a guard may not be asserted at all.
            let mut needed: Vec<Expr> = Vec::new();
            for g in &u.guards {
                outermost_apps(g, &mut needed);
            }
            if matches!(u.rhs, Expr::Call { .. } | Expr::Constructor { .. }) {
                needed.push(u.rhs.clone());
            }

            for t in needed {
                let ks = keys(shapes, &t);
                if ks.iter().any(|k| present.contains(k)) || !closed(&t) {
                    continue;
                }
                for sub in collect_ground_terms(&t) {
                    for k in keys(shapes, &sub) {
                        present.insert(k);
                    }
                }
                result.added.push(t);
            }

            if u.guards.is_empty() {
                if let Expr::Constructor { .. } = &u.rhs {
                    shapes.add_derived(app.clone(), u.rhs.clone());
                }
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::definitional_equations;
    use frontend::ast::{BaseType, BinOp, Program};
    use std::collections::HashMap;

    fn var(v: &str) -> Expr {
        Expr::Var(v.to_string())
    }
    fn ctor(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Constructor { name: name.to_string(), args }
    }
    fn call(f: &str, args: Vec<Expr>) -> Expr {
        Expr::Call { func: f.to_string(), args }
    }
    fn eq(l: Expr, r: Expr) -> Expr {
        Expr::BinOp { op: BinOp::Eq, left: Box::new(l), right: Box::new(r) }
    }
    fn and(l: Expr, r: Expr) -> Expr {
        Expr::BinOp { op: BinOp::And, left: Box::new(l), right: Box::new(r) }
    }
    fn peano() -> BaseType {
        BaseType::Custom("Peano".to_string())
    }

    fn program() -> Program {
        let mut program = Program { datatypes: HashMap::new(), functions: HashMap::new(), goals: Vec::new() };
        frontend::api::register_enum(&mut program, "Peano", "enum Peano { Zero, Succ(Box<Peano>) }");
        frontend::api::register_val(
            &mut program,
            "flag",
            None,
            "fn flag(x: Peano) -> bool { match x { Peano::Zero => true, Peano::Succ(_x1) => false } }",
            false,
        );
        frontend::api::register_val(
            &mut program,
            "plus",
            None,
            "fn plus(x: Peano, y: Peano) -> Peano { match x { Peano::Zero => y, Peano::Succ(x1) => Peano::Succ(Box::new(plus(*x1, y))) } }",
            true,
        );
        frontend::api::register_val(
            &mut program,
            "pick",
            None,
            "fn pick(x: Peano, y: Peano) -> Peano { match x { Peano::Zero => y, Peano::Succ(x1) => match y { Peano::Zero => x, Peano::Succ(y1) => if flag(*x1) { x } else { y } } } }",
            false,
        );
        program
    }

    // [ENG] A goal in the shape the checker produces: ∀binders. (path ∧ hyps) ⇒ target.
    fn goal(binders: &[&str], context: Vec<Expr>, target: Expr, instantiations: Vec<Expr>) -> Goal {
        let left = context.into_iter().reduce(and).unwrap_or(Expr::BoolConst(true));
        Goal {
            name: "g".to_string(),
            property: Expr::Forall {
                binders: binders.iter().map(|b| (b.to_string(), peano())).collect(),
                body: Box::new(Expr::BinOp { op: BinOp::Implies, left: Box::new(left), right: Box::new(target) }),
            },
            instantiations,
        }
    }

    #[test]
    fn a_literal_argument_unfolds_one_level_per_round() {
        let eqs = definitional_equations(&program());
        let two = ctor("Peano::Succ", vec![ctor("Peano::Succ", vec![ctor("Peano::Zero", vec![])])]);
        let one = ctor("Peano::Succ", vec![ctor("Peano::Zero", vec![])]);
        let target = eq(call("plus", vec![two, var("w")]), ctor("Peano::Succ", vec![ctor("Peano::Succ", vec![var("w")])]));
        let mut shapes = Shapes::default();

        let mut g = goal(&["w"], vec![], target, vec![]);
        let r1 = round(&eqs, &g, &mut shapes);
        // the whole rhs, one deep hint: its subterm plus(S(Z), w) comes with it
        assert_eq!(r1.added, vec![ctor("Peano::Succ", vec![call("plus", vec![one.clone(), var("w")])])]);
        assert!(r1.stuck.is_empty());

        g.instantiations.extend(r1.added);
        let r2 = round(&eqs, &g, &mut shapes);
        assert_eq!(r2.added, vec![ctor("Peano::Succ", vec![call("plus", vec![ctor("Peano::Zero", vec![]), var("w")])])]);

        g.instantiations.extend(r2.added);
        let r3 = round(&eqs, &g, &mut shapes);
        assert!(r3.added.is_empty(), "saturated: the base equation has no inner term");
    }

    #[test]
    fn the_hypothesis_term_is_present_and_the_shapeless_one_is_reported_stuck() {
        let eqs = definitional_equations(&program());
        // v = Succ(v1); IH names plus(v1, w); goal plus(v, w) == Succ(plus(v1, w))
        let target = eq(call("plus", vec![var("v"), var("w")]), ctor("Peano::Succ", vec![call("plus", vec![var("v1"), var("w")])]));
        let g = goal(&["v", "w", "v1"], vec![eq(var("v"), ctor("Peano::Succ", vec![var("v1")]))], target, vec![]);
        let mut shapes = Shapes::default();
        let r = round(&eqs, &g, &mut shapes);
        assert!(r.added.is_empty(), "the inner term plus(v1, w) is already named by the goal");
        assert_eq!(r.stuck, vec![call("plus", vec![var("v1"), var("w")])]);
        // the fired equation left a derived shape
        assert_eq!(
            shapes.shape_of(&call("plus", vec![var("v"), var("w")])),
            Some(&ctor("Peano::Succ", vec![call("plus", vec![var("v1"), var("w")])]))
        );
    }

    #[test]
    fn guards_are_candidates_and_are_added_once() {
        let eqs = definitional_equations(&program());
        let context = vec![
            eq(var("v"), ctor("Peano::Succ", vec![var("v1")])),
            eq(var("w"), ctor("Peano::Succ", vec![var("w1")])),
        ];
        let target = eq(call("pick", vec![var("v"), var("w")]), var("v"));
        let g = goal(&["v", "w", "v1", "w1"], context, target, vec![]);
        let mut shapes = Shapes::default();
        let r = round(&eqs, &g, &mut shapes);
        assert_eq!(r.added, vec![call("flag", vec![var("v1")])]);
        // a guarded leaf yields no derived shape
        assert_eq!(shapes.shape_of(&call("pick", vec![var("v"), var("w")])), None);
    }

    #[test]
    fn the_ledger_lists_every_application_inner_first_without_duplicates() {
        let eqs = definitional_equations(&program());
        let _ = eqs;
        let context = vec![eq(var("v"), ctor("Peano::Succ", vec![var("v1")]))];
        let target = eq(call("plus", vec![var("v"), var("w")]), call("plus", vec![var("v1"), var("w")]));
        let g = goal(&["v", "w", "v1"], context, target, vec![call("plus", vec![var("v1"), var("w")])]);
        let parts = dissect(&g.property);
        let l = ledger(&parts, &g.instantiations);
        assert_eq!(
            l,
            vec![
                ctor("Peano::Succ", vec![var("v1")]),
                call("plus", vec![var("v"), var("w")]),
                call("plus", vec![var("v1"), var("w")]),
            ]
        );
    }
}
