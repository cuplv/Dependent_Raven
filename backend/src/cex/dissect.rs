//! [KOR] VC 해부기.
//!
//! `Goal.property`(소스 수준 VC)를 반례 파일의 섹션들이 소비하는 조각으로
//! 분해합니다: 스콜렘 변수, path condition(패턴 바인딩), 가설(문맥의 사실,
//! 조건부일 수 있음), 그리고 goal. goal 쪽에서는 중첩된 함의를 벗겨
//! 전건들을 가정(assumptions)으로 모으고, 남은 핵심을 분류합니다:
//!
//! - `Core::Eq(lhs, rhs)`  -- 등식 goal. distinct assert + 양변 추적 대상.
//! - `Core::Bool(atom)`    -- 맨 술어 goal (예: eq_nat(x, x)).
//! - `Core::Opaque(expr)`  -- 그 외 전부. 인식 못 한 모양이라도 파일은
//!   포기하지 않습니다: goal 섹션만 통째-부정 렌더링으로 낮추고 나머지는
//!   온전히 방출하는 것이 소비자의 책임입니다.
//!
//! [ENG] The VC dissector.
//!
//! Breaks `Goal.property` (the source-level VC) into the pieces the
//! counterexample file's sections consume: skolem variables, path
//! conditions (pattern bindings), hypotheses (context facts, possibly
//! conditional), and the goal. On the goal side, nested implications are
//! peeled into assumptions, and the remaining core is classified:
//!
//! - `Core::Eq(lhs, rhs)`  -- an equality goal: distinct-assert + traces.
//! - `Core::Bool(atom)`    -- a bare predicate goal (e.g. eq_nat(x, x)).
//! - `Core::Opaque(expr)`  -- everything else. An unrecognized shape does
//!   not forfeit the file: consumers render the goal section as a
//!   wholesale negation and emit the rest at full quality.
//!
//! [KOR] 전체 골격(`Forall`의 본문이 `Implies`)은 실제 IR 덤프로 확인된
//! 불변식이므로(모듈 mod.rs 상단 참조) 어긋나면 panic합니다.
//! [ENG] The overall shell (a `Forall` whose body is an `Implies`) is an
//! invariant verified against real IR dumps (see the notes atop mod.rs),
//! so a mismatch panics.

use frontend::ast::{BaseType, BinOp, Expr, Ident};

/// [KOR] 해부된 VC.
/// [ENG] A dissected VC.
pub struct VcParts {
    /// [KOR] Forall 바인더 그대로 (Unit 타입 증명 배관 변수 포함).
    /// [ENG] The Forall binders verbatim (including Unit-typed proof plumbing).
    pub skolems: Vec<(Ident, BaseType)>,
    /// [KOR] `변수 == 생성자(..)` 꼴의 연언지: match 브랜치의 패턴 바인딩.
    /// [ENG] Conjuncts of shape `var == Constructor(..)`: the branch's
    ///       pattern bindings.
    pub path_conds: Vec<Expr>,
    /// [KOR] 나머지 문맥 사실들 (귀납 가설 등).
    /// [ENG] The remaining context facts (induction hypotheses etc.).
    pub hypotheses: Vec<Hypothesis>,
    pub goal: GoalShape,
}

/// [KOR] 문맥의 사실 하나. `implies(g, f)` 꼴이었다면 gate가 `Some(g)`이고,
///       그 사실은 gate가 참일 때만 쓸 수 있습니다.
/// [ENG] One context fact. If it was of shape `implies(g, f)`, gate is
///       `Some(g)` and the fact is usable only when the gate is true.
pub struct Hypothesis {
    pub gate: Option<Expr>,
    pub fact: Expr,
}

/// [KOR] goal: 벗겨낸 전건들(반례 모델에서 성립하는 가정)과 반증된 핵심.
/// [ENG] The goal: peeled antecedents (assumptions that hold in the
///       countermodel) and the falsified core.
pub struct GoalShape {
    pub assumptions: Vec<Expr>,
    pub core: Core,
}

pub enum Core {
    /// lhs == rhs
    Eq(Expr, Expr),
    /// [KOR] 맨 boolean 원자 (술어 호출 또는 변수).
    /// [ENG] A bare boolean atom (a predicate call or a variable).
    Bool(Expr),
    /// [KOR] 인식하지 못한 goal 모양. 소비자는 통째로 부정해 렌더링합니다.
    /// [ENG] An unrecognized goal shape. Consumers render it negated wholesale.
    Opaque(Expr),
}

/// [KOR] `Goal.property`를 해부합니다.
/// [ENG] Dissects a `Goal.property`.
pub fn dissect(property: &Expr) -> VcParts {
    let Expr::Forall { binders, body } = property else {
        panic!(
            "counterexample dissector: expected a Forall at the top of the VC, got {:?}",
            property
        );
    };
    let Expr::BinOp {
        op: BinOp::Implies,
        left,
        right,
    } = &**body
    else {
        panic!(
            "counterexample dissector: expected `context => goal` under the Forall, got {:?}",
            body
        );
    };

    let mut path_conds = Vec::new();
    let mut hypotheses = Vec::new();
    for conjunct in flatten_and(left) {
        if is_path_condition(conjunct) {
            path_conds.push(conjunct.clone());
        } else if let Expr::BinOp {
            op: BinOp::Implies,
            left: gate,
            right: fact,
        } = conjunct
        {
            hypotheses.push(Hypothesis {
                gate: Some((**gate).clone()),
                fact: (**fact).clone(),
            });
        } else {
            hypotheses.push(Hypothesis {
                gate: None,
                fact: conjunct.clone(),
            });
        }
    }

    VcParts {
        skolems: binders.clone(),
        path_conds,
        hypotheses,
        goal: dissect_goal(right),
    }
}

/// [KOR] And 트리를 연언지 목록으로 평탄화합니다. 채움용 `true`는 버립니다.
/// [ENG] Flattens an And tree into its conjuncts, dropping filler `true`.
fn flatten_and(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::BinOp {
            op: BinOp::And,
            left,
            right,
        } => {
            let mut out = flatten_and(left);
            out.extend(flatten_and(right));
            out
        }
        Expr::BoolConst(true) => Vec::new(),
        other => vec![other],
    }
}

fn is_path_condition(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        } if matches!(&**left, Expr::Var(_)) && matches!(&**right, Expr::Constructor { .. })
    )
}

/// [KOR] goal에서 중첩 함의를 벗겨 가정으로 모으고 핵심을 분류합니다.
///       `¬(P ⇒ Q)`는 `P ∧ ¬Q`이므로, 반례 모델에서 전건 P들은 성립하고
///       핵심 Q만 반증됩니다.
/// [ENG] Peels nested implications off the goal into assumptions and
///       classifies the core. Since `¬(P ⇒ Q)` is `P ∧ ¬Q`, the
///       antecedents P hold in the countermodel and only the core Q is
///       falsified.
fn dissect_goal(goal: &Expr) -> GoalShape {
    let mut assumptions = Vec::new();
    let mut core = goal;
    while let Expr::BinOp {
        op: BinOp::Implies,
        left,
        right,
    } = core
    {
        assumptions.push((**left).clone());
        core = right;
    }

    let core = match core {
        Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        } => Core::Eq((**left).clone(), (**right).clone()),
        Expr::Call { .. } | Expr::Var(_) => Core::Bool(core.clone()),
        other => Core::Opaque(other.clone()),
    };
    GoalShape { assumptions, core }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn call(func: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            func: func.to_string(),
            args,
        }
    }

    fn cons(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Constructor {
            name: name.to_string(),
            args,
        }
    }

    fn binop(op: BinOp, left: Expr, right: Expr) -> Expr {
        Expr::BinOp {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn nat() -> BaseType {
        BaseType::Custom("Nat".to_string())
    }

    fn forall(binders: Vec<(&str, BaseType)>, body: Expr) -> Expr {
        Expr::Forall {
            binders: binders
                .into_iter()
                .map(|(n, t)| (n.to_string(), t))
                .collect(),
            body: Box::new(body),
        }
    }

    /// The exact shape of prop_09's vc 6, as seen in the IR dump:
    /// forall i k j i_prime j_prime _bind_3 v_sub.
    ///   ((i == S(i_prime) && j == S(j_prime))
    ///     && sub(sub(i',j'),k) == sub(i',add(j',k))) && true
    ///   => sub(sub(i,j),k) == sub(i,add(j,k))
    fn prop_09_vc6() -> Expr {
        let ih = binop(
            BinOp::Eq,
            call(
                "sub",
                vec![
                    call("sub", vec![var("i_prime"), var("j_prime")]),
                    var("k"),
                ],
            ),
            call(
                "sub",
                vec![
                    var("i_prime"),
                    call("add", vec![var("j_prime"), var("k")]),
                ],
            ),
        );
        let antecedent = binop(
            BinOp::And,
            binop(
                BinOp::And,
                binop(
                    BinOp::And,
                    binop(BinOp::Eq, var("i"), cons("Nat::S", vec![var("i_prime")])),
                    binop(BinOp::Eq, var("j"), cons("Nat::S", vec![var("j_prime")])),
                ),
                ih,
            ),
            Expr::BoolConst(true),
        );
        let goal = binop(
            BinOp::Eq,
            call("sub", vec![call("sub", vec![var("i"), var("j")]), var("k")]),
            call(
                "sub",
                vec![var("i"), call("add", vec![var("j"), var("k")])],
            ),
        );
        forall(
            vec![
                ("i", nat()),
                ("k", nat()),
                ("j", nat()),
                ("i_prime", nat()),
                ("j_prime", nat()),
                ("_bind_3", BaseType::Unit),
                ("v_sub", BaseType::Unit),
            ],
            binop(BinOp::Implies, antecedent, goal),
        )
    }

    #[test]
    fn dissects_branch_vc_with_hypothesis() {
        let parts = dissect(&prop_09_vc6());
        assert_eq!(parts.skolems.len(), 7);
        assert_eq!(parts.path_conds.len(), 2);
        assert!(is_path_condition(&parts.path_conds[0]));
        assert_eq!(parts.hypotheses.len(), 1);
        assert!(parts.hypotheses[0].gate.is_none());
        assert!(matches!(&parts.hypotheses[0].fact,
            Expr::BinOp { op: BinOp::Eq, .. }));
        assert!(parts.goal.assumptions.is_empty());
        assert!(matches!(&parts.goal.core, Core::Eq(lhs, _)
            if matches!(lhs, Expr::Call { func, .. } if func == "sub")));
    }

    #[test]
    fn dissects_trivial_antecedent() {
        // prop_04's vc 1: forall n xs v_sub. true => S(count(n,xs)) == count(n,Cons(n,xs))
        let goal = binop(
            BinOp::Eq,
            cons("Nat::S", vec![call("count", vec![var("n"), var("xs")])]),
            call(
                "count",
                vec![var("n"), cons("NList::Cons", vec![var("n"), var("xs")])],
            ),
        );
        let vc = forall(
            vec![
                ("n", nat()),
                ("xs", BaseType::Custom("NList".to_string())),
                ("v_sub", BaseType::Unit),
            ],
            binop(BinOp::Implies, Expr::BoolConst(true), goal),
        );

        let parts = dissect(&vc);
        assert!(parts.path_conds.is_empty());
        assert!(parts.hypotheses.is_empty());
        assert!(matches!(parts.goal.core, Core::Eq(_, _)));
    }

    #[test]
    fn peels_implication_goal_into_assumptions() {
        // forall x y. true => (le(x, y) => max(x, y) == y)
        let goal = binop(
            BinOp::Implies,
            call("le", vec![var("x"), var("y")]),
            binop(
                BinOp::Eq,
                call("max", vec![var("x"), var("y")]),
                var("y"),
            ),
        );
        let vc = forall(
            vec![("x", nat()), ("y", nat())],
            binop(BinOp::Implies, Expr::BoolConst(true), goal),
        );

        let parts = dissect(&vc);
        assert_eq!(parts.goal.assumptions.len(), 1);
        assert!(matches!(&parts.goal.assumptions[0],
            Expr::Call { func, .. } if func == "le"));
        assert!(matches!(parts.goal.core, Core::Eq(_, _)));
    }

    #[test]
    fn conditional_context_fact_becomes_gated_hypothesis() {
        // Antecedent contains implies(le(a, b), max(a, b) == b).
        let gated = binop(
            BinOp::Implies,
            call("le", vec![var("a"), var("b")]),
            binop(
                BinOp::Eq,
                call("max", vec![var("a"), var("b")]),
                var("b"),
            ),
        );
        let goal = binop(BinOp::Eq, var("a"), var("b"));
        let vc = forall(
            vec![("a", nat()), ("b", nat())],
            binop(BinOp::Implies, gated, goal),
        );

        let parts = dissect(&vc);
        assert_eq!(parts.hypotheses.len(), 1);
        assert!(matches!(&parts.hypotheses[0].gate,
            Some(Expr::Call { func, .. }) if func == "le"));
    }

    #[test]
    fn bare_predicate_goal_is_bool_core() {
        // eq_refl style: forall x. true => eq_nat(x, x)
        let vc = forall(
            vec![("x", nat())],
            binop(
                BinOp::Implies,
                Expr::BoolConst(true),
                call("eq_nat", vec![var("x"), var("x")]),
            ),
        );
        assert!(matches!(dissect(&vc).goal.core, Core::Bool(_)));
    }

    #[test]
    fn unrecognized_goal_shape_falls_back_to_opaque() {
        // forall x y. true => (le(x, y) || le(y, x))
        let vc = forall(
            vec![("x", nat()), ("y", nat())],
            binop(
                BinOp::Implies,
                Expr::BoolConst(true),
                binop(
                    BinOp::Or,
                    call("le", vec![var("x"), var("y")]),
                    call("le", vec![var("y"), var("x")]),
                ),
            ),
        );
        assert!(matches!(dissect(&vc).goal.core, Core::Opaque(_)));
    }
}
