//! [KOR] 한 단계 전개: 장부의 적용 항 `f(args)`를, `f`의 정의 등식 중 인자 패턴이
//!       (알려진 모양으로 바꾼) 인자와 맞는 것들의 우변과 가드로 바꿉니다. 등식은
//!       `smt::DefEq` — solver에 보내는 공리와 같은 레코드입니다.
//! [ENG] One unfolding step: an application `f(args)` from the ledger becomes the
//!       right-hand sides and guards of those defining equations of `f` whose
//!       argument patterns match the (shape-expanded) arguments. The equations are
//!       `smt::DefEq`, the same record the solver's axioms are rendered from.

use frontend::ast::{BaseType, Expr, Ident};

use crate::frontier::shape::Shapes;
use crate::smt::DefEq;

/// [ENG] One matched equation, instantiated: its right-hand side and the guards
///       on the path to that leaf (`if` conditions, their negations, and
///       `x == e` let-equalities).
#[derive(Debug, Clone, PartialEq)]
pub struct Unfolding {
    pub rhs: Expr,
    pub guards: Vec<Expr>,
}

/// [KOR] 등식의 인자 패턴을 구체 인자에 한쪽 방향으로 맞춥니다. 패턴의 바인더는
///       무엇에든 맞고(같은 바인더가 두 번 나오면 두 항이 같아야 함), 생성자는 같은
///       이름·인자 수의 생성자에만 맞습니다. 구체 인자 쪽에 생성자가 필요한 자리에
///       변수나 적용이 오면 — 모양이 알려지지 않은 것 — 실패합니다.
/// [ENG] One-way match of an equation's argument patterns against concrete
///       arguments. A binder matches anything (a repeated binder must agree
///       structurally); a constructor pattern matches only the same constructor
///       with the same arity. A variable or application where the pattern wants a
///       constructor — an argument with no known shape — fails the match.
pub fn match_args(
    binders: &[(Ident, BaseType)],
    patterns: &[Expr],
    concrete: &[Expr],
) -> Option<Vec<(Ident, Expr)>> {
    if patterns.len() != concrete.len() {
        return None;
    }
    let mut subst: Vec<(Ident, Expr)> = Vec::new();
    for (p, c) in patterns.iter().zip(concrete) {
        if !match_one(binders, p, c, &mut subst) {
            return None;
        }
    }
    Some(subst)
}

fn match_one(binders: &[(Ident, BaseType)], p: &Expr, c: &Expr, subst: &mut Vec<(Ident, Expr)>) -> bool {
    match p {
        Expr::Var(b) if binders.iter().any(|(n, _)| n == b) => {
            match subst.iter().find(|(n, _)| n == b) {
                Some((_, bound)) => bound == c,
                None => {
                    subst.push((b.clone(), c.clone()));
                    true
                }
            }
        }
        Expr::Constructor { name, args } => match c {
            Expr::Constructor { name: cn, args: cargs } if cn == name && cargs.len() == args.len() => {
                args.iter().zip(cargs).all(|(pa, ca)| match_one(binders, pa, ca, subst))
            }
            _ => false,
        },
        // [ENG] A non-binder in a pattern (a nullary constructor rendered as a
        //       variable, or a free name) must occur verbatim.
        other => other == c,
    }
}

/// [KOR] 동시 대입: 바인더들을 한 번에 바꿉니다. 등식의 바인더 이름은 goal의 패턴
///       변수 이름과 자주 겹치므로(`t`, `h`) 순차 대입은 잘못된 결과를 냅니다.
/// [ENG] Simultaneous substitution of binders. Equation binders often share names
///       with the goal's own pattern variables (`t`, `h`), so sequential
///       substitution would capture; one pass avoids it. Leaves contain no binding
///       forms, so no shadowing arises.
pub fn subst_all(e: &Expr, subst: &[(Ident, Expr)]) -> Expr {
    match e {
        Expr::Var(v) => match subst.iter().find(|(n, _)| n == v) {
            Some((_, r)) => r.clone(),
            None => e.clone(),
        },
        Expr::Call { func, args } => Expr::Call {
            func: func.clone(),
            args: args.iter().map(|a| subst_all(a, subst)).collect(),
        },
        Expr::Constructor { name, args } => Expr::Constructor {
            name: name.clone(),
            args: args.iter().map(|a| subst_all(a, subst)).collect(),
        },
        Expr::BinOp { op, left, right } => Expr::BinOp {
            op: op.clone(),
            left: Box::new(subst_all(left, subst)),
            right: Box::new(subst_all(right, subst)),
        },
        Expr::UnOp { op, expr } => Expr::UnOp {
            op: op.clone(),
            expr: Box::new(subst_all(expr, subst)),
        },
        Expr::If { cond, then_expr, else_expr } => Expr::If {
            cond: Box::new(subst_all(cond, subst)),
            then_expr: Box::new(subst_all(then_expr, subst)),
            else_expr: Box::new(subst_all(else_expr, subst)),
        },
        Expr::Tuple(items) => Expr::Tuple(items.iter().map(|a| subst_all(a, subst)).collect()),
        other => other.clone(),
    }
}

/// [KOR] `app`을 한 단계 전개합니다: 머리 함수의 등식 중 인자 패턴이
///       `shapes.expand(args)`와 맞는 것마다 대입된 우변과 가드 하나. 맞는 등식이
///       없으면 빈 벡터 — 특히 어떤 인자에 맞춰 볼 생성자 모양이 없을 때.
/// [ENG] Unfolds `app` one step: one `Unfolding` per equation of its head whose
///       patterns match `shapes.expand(args)`. Empty when nothing matches — in
///       particular when an argument at a scrutinee position has no known shape.
pub fn unroll(eqs: &[DefEq], shapes: &Shapes, app: &Expr) -> Vec<Unfolding> {
    let Expr::Call { func, args } = app else {
        return Vec::new();
    };
    let expanded: Vec<Expr> = args.iter().map(|a| shapes.expand(a)).collect();
    eqs.iter()
        .filter(|e| &e.func == func)
        .filter_map(|e| {
            let subst = match_args(&e.binders, &e.args, &expanded)?;
            Some(Unfolding {
                rhs: subst_all(&e.rhs, &subst),
                guards: e.guards.iter().map(|g| subst_all(g, &subst)).collect(),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cex::dissect::{Core, GoalShape, VcParts};
    use crate::smt::definitional_equations;
    use frontend::ast::{BinOp, Program, UnOp};
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

    // [ENG] The same self-registered program as smt's test: a bool function, a
    //       recursive function, and a function with a nested match under an `if`.
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

    fn shapes(path_conds: Vec<Expr>) -> Shapes {
        Shapes::from_goal(&VcParts {
            skolems: vec![],
            path_conds,
            hypotheses: vec![],
            goal: GoalShape { assumptions: vec![], core: Core::Bool(var("p")) },
        })
    }

    #[test]
    fn a_shaped_argument_selects_the_matching_leaf() {
        let eqs = definitional_equations(&program());
        let s = shapes(vec![eq(var("v"), ctor("Peano::Succ", vec![var("v1")]))]);
        let got = unroll(&eqs, &s, &call("plus", vec![var("v"), var("w")]));
        assert_eq!(
            got,
            vec![Unfolding { rhs: ctor("Peano::Succ", vec![call("plus", vec![var("v1"), var("w")])]), guards: vec![] }]
        );
    }

    #[test]
    fn an_argument_without_a_shape_matches_nothing() {
        let eqs = definitional_equations(&program());
        let s = shapes(vec![]);
        assert!(unroll(&eqs, &s, &call("plus", vec![var("v"), var("w")])).is_empty());
        // the outer match succeeds but the inner scrutinee has no shape
        let s = shapes(vec![eq(var("v"), ctor("Peano::Succ", vec![var("v1")]))]);
        assert!(unroll(&eqs, &s, &call("pick", vec![var("v"), var("w")])).is_empty());
    }

    #[test]
    fn an_if_leaf_yields_both_branches_with_their_guards() {
        let eqs = definitional_equations(&program());
        let s = shapes(vec![
            eq(var("v"), ctor("Peano::Succ", vec![var("v1")])),
            eq(var("w"), ctor("Peano::Succ", vec![var("w1")])),
        ]);
        let got = unroll(&eqs, &s, &call("pick", vec![var("v"), var("w")]));
        assert_eq!(got.len(), 2);
        let guard = call("flag", vec![var("v1")]);
        assert!(got.contains(&Unfolding { rhs: ctor("Peano::Succ", vec![var("v1")]), guards: vec![guard.clone()] }));
        assert!(got.contains(&Unfolding {
            rhs: ctor("Peano::Succ", vec![var("w1")]),
            guards: vec![Expr::UnOp { op: UnOp::Not, expr: Box::new(guard) }],
        }));
    }

    #[test]
    fn a_literal_argument_needs_no_shape_entry() {
        let eqs = definitional_equations(&program());
        let s = shapes(vec![]);
        let two = ctor("Peano::Succ", vec![ctor("Peano::Succ", vec![ctor("Peano::Zero", vec![])])]);
        let got = unroll(&eqs, &s, &call("plus", vec![two, var("w")]));
        let one = ctor("Peano::Succ", vec![ctor("Peano::Zero", vec![])]);
        assert_eq!(got, vec![Unfolding { rhs: ctor("Peano::Succ", vec![call("plus", vec![one, var("w")])]), guards: vec![] }]);
    }

    #[test]
    fn substitution_is_simultaneous_when_goal_names_collide_with_binders() {
        let eqs = definitional_equations(&program());
        // the goal's variables are called `y` and `w`; the equation's binders are `x1`, `y`
        let s = shapes(vec![eq(var("v"), ctor("Peano::Succ", vec![var("y")]))]);
        let got = unroll(&eqs, &s, &call("plus", vec![var("v"), var("w")]));
        // x1 := y, y := w, applied at once: Succ(plus(y, w)), not Succ(plus(w, w))
        assert_eq!(
            got,
            vec![Unfolding { rhs: ctor("Peano::Succ", vec![call("plus", vec![var("y"), var("w")])]), guards: vec![] }]
        );
    }
}
