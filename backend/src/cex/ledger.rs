//! [KOR] 인스턴스화 항 장부.
//!
//! 실패한 질의의 인스턴스화 목록(정의됨 스위치)을 기원별로 묶어 주석
//! 블록으로 렌더링합니다. 기원은 타입체커가 쓴 것과 같은 수집기
//! (`auto_inst::collect_ground_terms`)를 VC의 각 조각에 따로 돌려서
//! 재계산합니다: goal(핵심 + 가정)에서 나온 항, 각 가설에서 나온 항,
//! path condition(패턴)에서 나온 항, 그리고 어느 조각도 내놓지 않은
//! 나머지 -- 사용자가 `instantiate!`로 직접 준 힌트.
//!
//! [ENG] The instantiated-terms ledger.
//!
//! Renders the failed query's instantiation list (its definedness
//! switches) as a comment block grouped by origin. Origins are recomputed
//! by running the same collector the type checker used
//! (`auto_inst::collect_ground_terms`) on each piece of the VC
//! separately: terms coming from the goal (core + assumptions), from each
//! hypothesis, from the path conditions (patterns), and whatever no piece
//! produced -- hints the user gave manually via `instantiate!`.
//!
//! [KOR] 항은 우선순위(goal > 가설들 > 패턴 > 힌트)에 따라 처음 맞는
//! 그룹 하나에만 나타나고, 그룹 안에서는 질의의 인스턴스화 순서를
//! 유지합니다.
//! [ENG] Each term appears in exactly one group, the first that claims it
//! (goal > hypotheses > patterns > hints), keeping the query's
//! instantiation order within a group.

use frontend::ast::{BinOp, Expr};
use frontend::auto_inst::collect_ground_terms;

use super::dissect::{Core, Hypothesis, VcParts};
use super::print::print_term;

/// [KOR] 장부 주석 블록을 만듭니다.
/// [ENG] Builds the ledger comment block.
pub fn print_ledger(parts: &VcParts, instantiations: &[Expr]) -> String {
    let goal_claims = goal_claim_terms(parts);
    let hyp_claims: Vec<(String, Vec<Expr>)> = parts
        .hypotheses
        .iter()
        .map(|h| (hypothesis_label(h), hypothesis_claim_terms(h)))
        .collect();
    let pattern_claims: Vec<Expr> = parts
        .path_conds
        .iter()
        .flat_map(|pc| collect_ground_terms(pc))
        .collect();

    // [KOR] 우선순위에 따라 각 인스턴스화 항을 한 그룹에 배정합니다.
    // [ENG] Assign each instantiated term to one group by priority.
    let mut goal_group = Vec::new();
    let mut hyp_groups: Vec<Vec<&Expr>> = vec![Vec::new(); hyp_claims.len()];
    let mut pattern_group = Vec::new();
    let mut hint_group = Vec::new();
    'terms: for term in instantiations {
        if goal_claims.contains(term) {
            goal_group.push(term);
            continue;
        }
        for (i, (_, claims)) in hyp_claims.iter().enumerate() {
            if claims.contains(term) {
                hyp_groups[i].push(term);
                continue 'terms;
            }
        }
        if pattern_claims.contains(term) {
            pattern_group.push(term);
        } else {
            hint_group.push(term);
        }
    }

    let mut out = String::from("; instantiated terms:\n");
    push_group(&mut out, "from the goal:", &goal_group);
    for ((label, _), group) in hyp_claims.iter().zip(&hyp_groups) {
        push_group(&mut out, label, group);
    }
    push_group(&mut out, "from patterns:", &pattern_group);
    push_group(&mut out, "user hints (instantiate!):", &hint_group);
    out
}

/// [KOR] goal이 내놓는 항: 핵심의 양변(또는 원자)과 가정들에서 수집.
/// [ENG] Terms the goal yields: collected from the core's sides (or atom)
///       and from the assumptions.
fn goal_claim_terms(parts: &VcParts) -> Vec<Expr> {
    let mut claims = Vec::new();
    match &parts.goal.core {
        Core::Eq(lhs, rhs) => {
            claims.extend(collect_ground_terms(lhs));
            claims.extend(collect_ground_terms(rhs));
        }
        Core::Bool(atom) => claims.extend(collect_ground_terms(atom)),
        Core::Opaque(expr) => claims.extend(collect_ground_terms(expr)),
    }
    for assumption in &parts.goal.assumptions {
        claims.extend(collect_ground_terms(assumption));
    }
    claims
}

fn hypothesis_claim_terms(h: &Hypothesis) -> Vec<Expr> {
    let mut claims = collect_ground_terms(&h.fact);
    if let Some(gate) = &h.gate {
        claims.extend(collect_ground_terms(gate));
    }
    claims
}

/// [KOR] 가설 그룹의 라벨: 사실 자체를 찍어 보여줍니다. (그 사실을 만든
///       호출의 이름은 VC에 남아 있지 않으므로, 사실을 보여주는 것이
///       정직하고 충분합니다.)
/// [ENG] The label of a hypothesis group: the fact itself, printed. (The
///       name of the call that produced the fact is not recorded in the
///       VC; showing the fact is honest and sufficient.)
fn hypothesis_label(h: &Hypothesis) -> String {
    let fact = render_fact(&h.fact);
    match &h.gate {
        Some(gate) => format!("from the hypothesis implies({}, {}):", render_fact(gate), fact),
        None => format!("from the hypothesis {}:", fact),
    }
}

fn render_fact(fact: &Expr) -> String {
    match fact {
        Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        } => format!("{} == {}", print_term(left), print_term(right)),
        other => print_term(other),
    }
}

fn push_group(out: &mut String, label: &str, terms: &[&Expr]) {
    if terms.is_empty() {
        return;
    }
    out.push_str(&format!(";   {}\n", label));
    let rendered: Vec<String> = terms.iter().map(|t| print_term(t)).collect();
    out.push_str(&format!(";     {}\n", rendered.join("   ")));
}

#[cfg(test)]
mod tests {
    use frontend::ast::BaseType;

    use super::super::dissect::dissect;
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

    /// prop_09 vc 6 shaped VC (see dissect.rs tests for the source dump).
    fn prop_09_vc6() -> Expr {
        let nat = || BaseType::Custom("Nat".to_string());
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
                binop(BinOp::Eq, var("i"), cons("Nat::S", vec![var("i_prime")])),
                binop(BinOp::Eq, var("j"), cons("Nat::S", vec![var("j_prime")])),
            ),
            ih,
        );
        let goal = binop(
            BinOp::Eq,
            call("sub", vec![call("sub", vec![var("i"), var("j")]), var("k")]),
            call(
                "sub",
                vec![var("i"), call("add", vec![var("j"), var("k")])],
            ),
        );
        Expr::Forall {
            binders: vec![
                ("i".to_string(), nat()),
                ("k".to_string(), nat()),
                ("j".to_string(), nat()),
                ("i_prime".to_string(), nat()),
                ("j_prime".to_string(), nat()),
            ],
            body: Box::new(binop(BinOp::Implies, antecedent, goal)),
        }
    }

    #[test]
    fn partitions_terms_by_origin() {
        let parts = dissect(&prop_09_vc6());
        // The query's instantiation list: four goal terms, four hypothesis
        // terms, two pattern terms, and one manual hint that no VC piece
        // yields (the restored instantiate! of prop_09).
        let instantiations = vec![
            call("sub", vec![var("i"), var("j")]),
            call("sub", vec![call("sub", vec![var("i"), var("j")]), var("k")]),
            call("add", vec![var("j"), var("k")]),
            call(
                "sub",
                vec![var("i"), call("add", vec![var("j"), var("k")])],
            ),
            call("sub", vec![var("i_prime"), var("j_prime")]),
            call(
                "sub",
                vec![
                    call("sub", vec![var("i_prime"), var("j_prime")]),
                    var("k"),
                ],
            ),
            call("add", vec![var("j_prime"), var("k")]),
            call(
                "sub",
                vec![
                    var("i_prime"),
                    call("add", vec![var("j_prime"), var("k")]),
                ],
            ),
            cons("Nat::S", vec![var("i_prime")]),
            cons("Nat::S", vec![var("j_prime")]),
            cons("Nat::S", vec![call("add", vec![var("j_prime"), var("k")])]),
        ];

        assert_eq!(
            print_ledger(&parts, &instantiations),
            "; instantiated terms:\n\
             ;   from the goal:\n\
             ;     (sub i j)   (sub (sub i j) k)   (add j k)   (sub i (add j k))\n\
             ;   from the hypothesis (sub (sub i_prime j_prime) k) == (sub i_prime (add j_prime k)):\n\
             ;     (sub i_prime j_prime)   (sub (sub i_prime j_prime) k)   (add j_prime k)   (sub i_prime (add j_prime k))\n\
             ;   from patterns:\n\
             ;     (S i_prime)   (S j_prime)\n\
             ;   user hints (instantiate!):\n\
             ;     (S (add j_prime k))\n"
        );
    }

    #[test]
    fn empty_groups_are_omitted() {
        // prop_04 style: no path conditions, no hypotheses.
        let goal = binop(
            BinOp::Eq,
            cons("Nat::S", vec![call("count", vec![var("n"), var("xs")])]),
            call(
                "count",
                vec![var("n"), cons("NList::Cons", vec![var("n"), var("xs")])],
            ),
        );
        let vc = Expr::Forall {
            binders: vec![("n".to_string(), BaseType::Custom("Nat".to_string()))],
            body: Box::new(binop(BinOp::Implies, Expr::BoolConst(true), goal)),
        };
        let parts = dissect(&vc);
        let instantiations = vec![
            call("count", vec![var("n"), var("xs")]),
            cons("Nat::S", vec![call("count", vec![var("n"), var("xs")])]),
            cons("NList::Cons", vec![var("n"), var("xs")]),
        ];

        let ledger = print_ledger(&parts, &instantiations);
        assert!(ledger.contains("from the goal:"));
        assert!(!ledger.contains("from patterns:"));
        assert!(!ledger.contains("hypothesis"));
        assert!(!ledger.contains("user hints"));
    }
}
