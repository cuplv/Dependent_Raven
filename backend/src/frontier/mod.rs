//! [KOR] 기호적 경계(symbolic frontier): 정의를 goal의 분기가 고정한 생성자 모양에
//!       맞춰 기호적으로 전개하여, 질의에 없는 적용 항을 자동으로 인스턴스화합니다.
//!       solver 모델은 읽지 않습니다. 계획: `doc/auto_instantiation_plan.md`.
//!       `shape`(모양 환경), `unroll`(한 단계 전개), `candidates`(한 라운드의 후보);
//!       라운드 루프는 `smt::encode_and_solve`에 있고, 이 파일은 스위치와 보고입니다.
//! [ENG] The symbolic frontier: automatic instantiation by unfolding definitions
//!       against the constructor shapes a goal's branch fixes, never against a
//!       solver model. Plan: `doc/auto_instantiation_plan.md`. `shape` (the shape
//!       environment), `unroll` (one unfolding step), `candidates` (one round's
//!       candidates); the round loop lives in `smt::encode_and_solve`, and this
//!       file holds the switches and the report.

pub mod candidates;
pub mod shape;
pub mod unroll;

use frontend::ast::{Expr, Goal};

use crate::cex::dissect::dissect;
use crate::frontier::candidates::Round;

/// [KOR] 환경 변수로 켜고 끄는 스위치.
///   RAVENCHECK_AUTO_INST=0        루프를 끕니다 (기본은 켜짐)
///   RAVENCHECK_AUTO_INST=suggest  한 라운드만 계산해 후보를 출력하고 더하지 않음
///   RAVENCHECK_AUTO_INST_DEPTH=N  goal당 라운드 상한 (기본 8)
///   RAVENCHECK_AUTO_INST_TRACE=1  라운드마다 더한 항을 출력
/// [ENG] Switches, from the environment:
///   RAVENCHECK_AUTO_INST=0        turn the loop off (on by default)
///   RAVENCHECK_AUTO_INST=suggest  compute one round, print the candidates, add nothing
///   RAVENCHECK_AUTO_INST_DEPTH=N  cap on rounds per goal (default 8)
///   RAVENCHECK_AUTO_INST_TRACE=1  print each round's terms as they are added
#[derive(Debug, Clone)]
pub struct Config {
    pub enabled: bool,
    pub suggest: bool,
    pub depth: usize,
    pub trace: bool,
}

impl Config {
    pub fn from_env() -> Config {
        let mode = std::env::var("RAVENCHECK_AUTO_INST").unwrap_or_default();
        let enabled = mode != "0";
        let depth = std::env::var("RAVENCHECK_AUTO_INST_DEPTH")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8);
        Config {
            enabled,
            suggest: mode == "suggest",
            depth,
            trace: std::env::var("RAVENCHECK_AUTO_INST_TRACE").is_ok(),
        }
    }
}

/// [ENG] Why the loop stopped without a proof. Only `Saturated` is evidence that
///       a lemma is missing; `Limited` says nothing about the goal.
#[derive(Debug, Clone)]
pub enum Stop {
    Saturated { stuck: Vec<Expr> },
    Limited { depth: usize },
}

/// [KOR] 항을 `instantiate!` 안에 붙여 넣을 수 있는 소스 문법으로 렌더링합니다
///       (`Nat::S(max(a_min, b_min))`; 매크로 안이므로 `Box::new`는 필요 없음).
/// [ENG] A term in source syntax, paste-ready inside `instantiate!` (no
///       `Box::new`: the macro's argument is recorded, not compiled).
pub fn render(e: &Expr) -> String {
    match e {
        Expr::Var(v) => v.clone(),
        Expr::BoolConst(b) => b.to_string(),
        Expr::Call { func, args } => format!("{}({})", func, render_args(args)),
        Expr::Constructor { name, args } if args.is_empty() => name.clone(),
        Expr::Constructor { name, args } => format!("{}({})", name, render_args(args)),
        Expr::BinOp { op, left, right } => format!("({} {:?} {})", render(left), op, render(right)),
        Expr::UnOp { expr, .. } => format!("!{}", render(expr)),
        other => format!("{:?}", other),
    }
}

fn render_args(args: &[Expr]) -> String {
    args.iter().map(render).collect::<Vec<_>>().join(", ")
}

/// [ENG] The goal's branch, as `v = C(..)` pairs, for the report.
fn branch_line(goal: &Goal) -> String {
    let parts = dissect(&goal.property);
    let conds: Vec<String> = parts
        .path_conds
        .iter()
        .map(|c| match c {
            Expr::BinOp { left, right, .. } => format!("{} = {}", render(left), render(right)),
            other => render(other),
        })
        .collect();
    if conds.is_empty() {
        String::from("(no branch)")
    } else {
        conds.join(", ")
    }
}

/// [ENG] After a goal verified with the engine's help: the hints to paste, by round.
pub fn verified_report(rounds: &[Vec<Expr>], goal: Option<&Goal>) -> String {
    let mut out = String::new();
    let total: usize = rounds.iter().map(|r| r.len()).sum();
    out.push_str(&format!(
        "  🔁 auto-instantiation: {} term(s) in {} round(s)",
        total,
        rounds.len()
    ));
    if let Some(g) = goal {
        out.push_str(&format!(" — branch {}", branch_line(g)));
    }
    out.push('\n');
    for (i, r) in rounds.iter().enumerate() {
        for t in r {
            out.push_str(&format!("       round {}: instantiate!({});\n", i + 1, render(t)));
        }
    }
    out
}

/// [ENG] Appended to a failing goal's report when the engine ran.
pub fn stop_report(stop: &Stop, rounds: &[Vec<Expr>]) -> String {
    let mut out = String::new();
    match stop {
        Stop::Saturated { stuck } => {
            out.push_str(&format!(
                "\n## > 🔁 Auto-instantiation: saturated after {} round(s); a round adds nothing.",
                rounds.len()
            ));
            if !stuck.is_empty() {
                out.push_str("\n## >    stuck (no equation matches, an argument has no shape):");
                for t in stuck {
                    out.push_str(&format!("\n## >      {}", render(t)));
                }
            }
        }
        Stop::Limited { depth } => out.push_str(&format!(
            "\n## > 🔁 Auto-instantiation: limited at depth {}; not saturated, no conclusion.",
            depth
        )),
    }
    let total: usize = rounds.iter().map(|r| r.len()).sum();
    if total > 0 {
        out.push_str(&format!("\n## >    added before stopping ({}):", total));
        for (i, r) in rounds.iter().enumerate() {
            for t in r {
                out.push_str(&format!("\n## >      round {}: instantiate!({});", i + 1, render(t)));
            }
        }
    }
    out
}

/// [ENG] `RAVENCHECK_AUTO_INST=suggest`: one round's candidates and stuck terms,
///       printed, nothing added.
pub fn suggestion(round: &Round) -> String {
    let mut out = String::from("  🔁 auto-instantiation (suggest): ");
    if round.added.is_empty() {
        out.push_str("no candidate");
    } else {
        out.push_str(&format!("{} candidate(s)", round.added.len()));
        for t in &round.added {
            out.push_str(&format!("\n       instantiate!({});", render(t)));
        }
    }
    for t in &round.stuck {
        out.push_str(&format!("\n       stuck: {}", render(t)));
    }
    out
}
