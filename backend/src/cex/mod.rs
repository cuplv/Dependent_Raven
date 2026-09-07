//! [KOR] 반례(counterexample) 파일 생성기.
//!
//! 검증에 실패한 목표(Goal)에 대해, 사용자가 소스 프로그램에 쓴 어휘만으로
//! (변수/함수/생성자 이름 그대로, `anf_*`나 `*_rel` 같은 내부 이름 없이)
//! 반례 모델을 설명하는 SMT-LIB 파일을 logs/ 폴더에 씁니다.
//! 이 파일은 설명용 산출물입니다: 생성 후 다시 solver로 검사하지 않습니다.
//!
//! [ENG] Counterexample file emitter.
//!
//! For a goal that failed verification, writes an SMT-LIB file into logs/
//! describing the countermodel using only the vocabulary of the user's
//! source program (variable/function/constructor names as written; no
//! internal names like `anf_*` or `*_rel`). The file is an explanatory
//! artifact: it is never fed back to the solver after generation.
//!
//! ---------------------------------------------------------------------
//! [KOR] 이 모듈이 의존하는, 실제 IR 덤프로 확인한 파이프라인 사실들:
//! [ENG] Pipeline facts this module relies on, verified against IR dumps:
//!
//! 1. `Goal.property`는 소스 수준(ANF 이전) 식이며, 모양은
//!    `Forall { binders, body: Implies { left, right } }`이다.
//!    - `left`(전제)는 왼쪽으로 중첩된 And 트리이거나 `BoolConst(true)`.
//!      match 브랜치의 패턴 바인딩은 `Eq(Var, Constructor)` 연언지로,
//!      문맥의 사실(예: 귀납 가설)은 그 외의 연언지로 들어 있다.
//!    - `right`(결론)가 증명하려는 성질이다.
//!    - binders에는 Unit 타입 변수(`v_sub`, `_bind_*`)도 섞여 있다.
//!    `Goal.property` is a source-level (pre-ANF) expression shaped
//!    `Forall { binders, body: Implies { left, right } }`. `left` (the
//!    antecedent) is a left-nested And tree, or `BoolConst(true)`:
//!    pattern bindings appear as `Eq(Var, Constructor)` conjuncts, and
//!    context facts (e.g. induction hypotheses) as the remaining
//!    conjuncts. `right` is the property to prove. The binders include
//!    Unit-typed variables (`v_sub`, `_bind_*`).
//!
//! 2. 논리적 함의는 전용 노드 `BinOp::Implies`로 표현된다
//!    (소스 문법: `implies(p, q)`).
//!    Logical implication is the dedicated node `BinOp::Implies`
//!    (source syntax: `implies(p, q)`).
//!
//! 3. easy-smt(0.2.8)의 세션은 check() 이후에도 push/pop, declare_const,
//!    assert, 재-check, get_value를 지원한다. 모델 값이 필요해지면 이미
//!    열려 있는 그 세션에서 읽으면 되고, 질의를 재실행할 필요가 없다.
//!    The live easy-smt (0.2.8) session supports push/pop, declare_const,
//!    assert, re-check, and get_value after check(); model values, when
//!    needed, come from the already-open session -- no query re-run.

pub mod defs;
pub mod dissect;
pub mod ledger;
pub mod print;

use std::collections::BTreeSet;
use std::fs;

use frontend::ast::{BinOp, Expr, Goal, Program};

use dissect::{Core, VcParts};

/// [KOR] 실패한 goal에 대한 반례 파일을 `path`에 씁니다.
///       호출자는 에러(와 panic)를 경고로만 다루어야 합니다: 반례 생성
///       실패가 검증 실패 보고 자체를 가려서는 안 됩니다.
/// [ENG] Writes the counterexample file for a failed goal to `path`.
///       Callers must treat errors (and panics) as warnings only: a
///       failure to emit the counterexample must never mask the
///       verification failure.
pub fn emit(program: &Program, goal: &Goal, path: &str) -> Result<(), String> {
    let parts = dissect::dissect(&goal.property);
    let terms: Vec<&Expr> = goal.instantiations.iter().collect();

    // [KOR] 파일에 등장할 함수들: 인스턴스화 목록이 goal/문맥/패턴에서
    //       수집된 상위 집합이므로 그것만 걸으면 충분합니다.
    // [ENG] The functions appearing in the file: the instantiation list is
    //       a superset collected from goal/context/patterns, so walking it
    //       is sufficient.
    let mut funcs = BTreeSet::new();
    let mut enums = BTreeSet::new();
    for term in &goal.instantiations {
        print::collect_symbols(term, &mut funcs, &mut enums);
    }

    let mut out = String::new();
    out.push_str("; ravencheck counterexample\n");
    out.push_str(&format!("; lemma  : {}\n", lemma_line(&goal.name)));
    out.push_str(&format!("; goal   : {}\n", render_goal(&parts)));
    if !parts.path_conds.is_empty() {
        let branch: Vec<String> = parts
            .path_conds
            .iter()
            .map(|pc| {
                let (lhs, rhs) = eq_sides(pc);
                format!(
                    "{} = {}",
                    defs::render_expr(lhs, &[]),
                    defs::render_expr(rhs, &[])
                )
            })
            .collect();
        out.push_str(&format!("; branch : {}\n", branch.join(", ")));
    }

    let definitions = defs::print_definitions(program, &funcs);
    if !definitions.is_empty() {
        out.push_str(";\n");
        out.push_str(&definitions);
    }

    out.push('\n');
    out.push_str(&print::print_declarations(program, &terms, &parts.skolems));

    if !parts.path_conds.is_empty() {
        out.push('\n');
        for pc in &parts.path_conds {
            let (lhs, rhs) = eq_sides(pc);
            out.push_str(&format!(
                "(assert (= {} {}))\n",
                print::print_term(lhs),
                print::print_term(rhs)
            ));
        }
    }

    out.push('\n');
    out.push_str(&ledger::print_ledger(&parts, &goal.instantiations));

    out.push('\n');
    // [KOR] goal이 함의였다면 전건들은 반례 모델에서 성립합니다.
    // [ENG] If the goal was an implication, its antecedents hold in the
    //       countermodel.
    for assumption in &parts.goal.assumptions {
        out.push_str(&format!("(assert {})\n", holding_fact_sexpr(assumption)));
    }
    match &parts.goal.core {
        Core::Eq(lhs, rhs) => out.push_str(&format!(
            "(assert (distinct {} {}))\n",
            print::print_term(lhs),
            print::print_term(rhs)
        )),
        Core::Bool(atom) => {
            out.push_str(&format!("(assert (= {} false))\n", print::print_term(atom)))
        }
        Core::Opaque(_) => {
            out.push_str("; goal shape not recognized; negated-goal assert omitted\n")
        }
    }
    out.push_str("(check-sat)\n");

    fs::write(path, out).map_err(|e| e.to_string())
}

/// [KOR] "tip_nine_vc_6" -> "tip_nine   [vc 6]". 이름이 그 규칙을 따르지
///       않으면 그대로 씁니다.
/// [ENG] "tip_nine_vc_6" -> "tip_nine   [vc 6]". Names not following that
///       convention are used verbatim.
fn lemma_line(name: &str) -> String {
    match name.rsplit_once("_vc_") {
        Some((base, n)) => format!("{}   [vc {}]", base, n),
        None => name.to_string(),
    }
}

/// [KOR] 헤더의 goal 한 줄을 수학 표기로 만듭니다:
///       `가정 ==> ... ==> 핵심`.
/// [ENG] Builds the header's goal line in math notation:
///       `assumption ==> ... ==> core`.
fn render_goal(parts: &VcParts) -> String {
    let core = match &parts.goal.core {
        Core::Eq(lhs, rhs) => format!(
            "{} == {}",
            defs::render_expr(lhs, &[]),
            defs::render_expr(rhs, &[])
        ),
        Core::Bool(atom) => defs::render_expr(atom, &[]),
        // [KOR] 인식 못 한 모양에는 아직 예쁜 표기가 없습니다.
        // [ENG] No pretty form for unrecognized shapes yet.
        Core::Opaque(expr) => format!("{:?}", expr),
    };
    parts
        .goal
        .assumptions
        .iter()
        .rev()
        .fold(core, |acc, a| format!("{} ==> {}", math_fact(a), acc))
}

/// [KOR] 사실 하나의 수학 표기: 등식은 `a == b`, 그 외는 항 그대로.
/// [ENG] Math notation for one fact: equalities as `a == b`, otherwise the
///       term itself.
fn math_fact(fact: &Expr) -> String {
    match fact {
        Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        } => format!(
            "{} == {}",
            defs::render_expr(left, &[]),
            defs::render_expr(right, &[])
        ),
        Expr::BinOp {
            op: BinOp::Neq,
            left,
            right,
        } => format!(
            "{} != {}",
            defs::render_expr(left, &[]),
            defs::render_expr(right, &[])
        ),
        // Negated facts are formulas; keep them away from the term
        // renderer. A negated equality is written as != (a bare
        // "!a == b" would read as (!a) == b).
        Expr::UnOp {
            op: frontend::ast::UnOp::Not,
            expr,
        } => match &**expr {
            Expr::BinOp {
                op: BinOp::Eq,
                left,
                right,
            } => format!(
                "{} != {}",
                defs::render_expr(left, &[]),
                defs::render_expr(right, &[])
            ),
            inner => format!("!{}", math_fact(inner)),
        },
        other => defs::render_expr(other, &[]),
    }
}

/// [KOR] 반례 모델에서 성립하는 사실 하나를 s-식으로: 등식은 `(= a b)`,
///       boolean 원자는 `(= atom true)`.
/// [ENG] One fact holding in the countermodel, as an s-expression:
///       equalities as `(= a b)`, boolean atoms as `(= atom true)`.
fn holding_fact_sexpr(fact: &Expr) -> String {
    match fact {
        Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        } => format!("(= {} {})", print::print_term(left), print::print_term(right)),
        Expr::BinOp {
            op: BinOp::Neq,
            left,
            right,
        } => format!(
            "(distinct {} {})",
            print::print_term(left),
            print::print_term(right)
        ),
        // A negated fact holds when its inner fact does not.
        Expr::UnOp {
            op: frontend::ast::UnOp::Not,
            expr,
        } => format!("(not {})", holding_fact_sexpr(expr)),
        other => format!("(= {} true)", print::print_term(other)),
    }
}

fn eq_sides(expr: &Expr) -> (&Expr, &Expr) {
    match expr {
        Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        } => (left, right),
        other => panic!(
            "counterexample emitter: expected an equality, got {:?}",
            other
        ),
    }
}
