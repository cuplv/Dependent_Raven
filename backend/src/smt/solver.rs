//! backend/src/smt/solver.rs
//! SMT 질의 파일 작성과 솔버 프로세스 실행을 담당하는 모듈
//!
//! [ENG] A goal's query is written to a file as SMT-LIB text (the replay artifact)
//! and solved in-process by z3 through its API, with no time limit, one run per
//! goal. When the answer is `sat`, the finite model of that same run is returned
//! with the verdict, so the countermodel costs no second solve. z3's own
//! `unknown`, and any error it raises (out of memory), are reported as
//! `Unknown`.
//!
//! `RAVENCHECK_SOLVER=cvc5` keeps the earlier subprocess race (cvc5
//! `--full-saturate-quant` against `--finite-model-find`, first definite answer
//! wins), which yields no model.
//! [KOR] goal의 질의를 SMT-LIB 텍스트 파일로 쓰고(재생용), z3 API로 프로세스 안에서
//! 시간 제한 없이 한 번 풉니다. 답이 `sat`이면 그 실행의 유한 모델을 함께 돌려주므로
//! 반례 모델에 두 번째 풀이가 들지 않습니다. z3의 `unknown`과 오류(메모리 부족)는
//! `Unknown`으로 보고합니다.

use crate::model::Model;
use easy_smt::{Context, ContextBuilder, SExpr};
use std::fs;
use std::io::Read;
use std::process::{Child, Command, Stdio};
use std::time::Duration;

/// [KOR] 솔버의 답. `Unknown`은 확정 답이 없었다는 뜻입니다(z3의 unknown 또는 오류).
/// [ENG] The solver's answer. `Unknown`: no definitive answer (z3's own unknown,
///       or an error such as out of memory).
#[derive(Debug, PartialEq)]
pub enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// [KOR] 하나의 goal에 대한 SMT-LIB 질의를 텍스트로 쌓습니다. `smt`는 식을 만들고
///       출력하는 데만 쓰이는, 솔버 없는 easy-smt 컨텍스트입니다.
/// [ENG] Accumulates one goal's SMT-LIB query as text. `smt` is a solver-less
///       easy-smt context, used only to build and print expressions.
pub struct Query {
    pub smt: Context,
    text: String,
}

impl Query {
    pub fn new() -> Self {
        let smt = ContextBuilder::new().build().expect("Failed to build SMT context");
        Query { smt, text: String::from("(set-logic ALL)\n") }
    }

    pub fn atom(&self, name: impl Into<String> + AsRef<str>) -> SExpr {
        self.smt.atom(name)
    }

    fn command(&mut self, parts: Vec<SExpr>) {
        let cmd = self.smt.list(parts);
        self.text.push_str(&format!("{}\n", self.smt.display(cmd)));
    }

    pub fn declare_sort(&mut self, name: String) {
        let parts = vec![self.smt.atom("declare-sort"), self.smt.atom(name), self.smt.atom("0")];
        self.command(parts);
    }

    pub fn declare_const(&mut self, name: String, sort: SExpr) {
        let parts = vec![self.smt.atom("declare-const"), self.smt.atom(name), sort];
        self.command(parts);
    }

    pub fn declare_fun(&mut self, name: String, args: Vec<SExpr>, out: SExpr) {
        let args = self.smt.list(args);
        let parts = vec![self.smt.atom("declare-fun"), self.smt.atom(name), args, out];
        self.command(parts);
    }

    pub fn assert(&mut self, expr: SExpr) {
        let parts = vec![self.smt.atom("assert"), expr];
        self.command(parts);
    }

    /// [ENG] Writes the query, closed by `(check-sat)`, to `path` and solves it.
    /// [ENG] Writes the query, closed by `(check-sat)`, to `path` and solves it.
    ///       The model is `Some` only for a `sat` answer from z3.
    pub fn solve(&self, path: &str) -> (Verdict, Option<Model>) {
        let text = format!("{}(check-sat)\n", self.text);
        fs::write(path, &text).unwrap_or_else(|e| panic!("Failed to write SMT query {}: {}", path, e));
        match std::env::var("RAVENCHECK_SOLVER").as_deref() {
            Ok("cvc5") => (solve_with_cvc5(path), None),
            Ok(other) if other != "z3" => panic!("RAVENCHECK_SOLVER must be `z3` or `cvc5`, got `{}`", other),
            _ => crate::model::z3::solve(&text),
        }
    }
}

/// [ENG] The subprocess race kept for `RAVENCHECK_SOLVER=cvc5`: the prover and
///       the model finder run on the query file without a time limit; the first
///       definite answer decides and the other process is killed.
fn solve_with_cvc5(path: &str) -> Verdict {
    let mut running: Vec<Child> = ["--full-saturate-quant", "--finite-model-find"]
        .iter()
        .map(|strategy| spawn("cvc5", &["--lang", "smt2", strategy, path]))
        .collect();

    let mut verdict = Verdict::Unknown;
    while !running.is_empty() && verdict == Verdict::Unknown {
        let mut still_running = Vec::new();
        for mut child in running {
            match child.try_wait().expect("Failed to poll the solver process") {
                Some(_) if verdict == Verdict::Unknown => verdict = read_verdict(&mut child),
                Some(_) => {}
                None => still_running.push(child),
            }
        }
        running = still_running;
        if verdict == Verdict::Unknown {
            std::thread::sleep(Duration::from_millis(2));
        }
    }
    for mut child in running {
        let _ = child.kill();
        let _ = child.wait();
    }
    verdict
}

fn spawn(program: &str, args: &[&str]) -> Child {
    Command::new(program)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap_or_else(|e| panic!(
            "Failed to start `{}` ({}); install it, or unset RAVENCHECK_SOLVER to use z3 in-process",
            program, e
        ))
}

/// [ENG] The first line of a finished solver's output. Anything but `sat`/`unsat`
///       (`unknown`, a timeout message, an error) is not a definitive answer.
fn read_verdict(child: &mut Child) -> Verdict {
    let mut out = String::new();
    if let Some(stdout) = child.stdout.as_mut() {
        let _ = stdout.read_to_string(&mut out);
    }
    match out.lines().next().map(str::trim) {
        Some("sat") => Verdict::Sat,
        Some("unsat") => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}
