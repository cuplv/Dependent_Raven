//! backend/src/smt/solver.rs
//! SMT 질의 파일 작성과 솔버 프로세스 실행을 담당하는 모듈
//!
//! [ENG] A goal's query is written to a file as SMT-LIB text and the solver runs on
//! that file as a subprocess. Owning the process (instead of talking to one over an
//! interactive pipe) is what allows a race between two solver configurations:
//!
//!   - `cvc5 --full-saturate-quant`  proves (unsat), but does not terminate on a
//!     satisfiable query of AVL size;
//!   - `cvc5 --finite-model-find`    finds the countermodel (sat) quickly, but does
//!     not terminate on the hard unsat queries.
//!
//! Every query is in EPR, so exactly one of the two is in its element; the first
//! definitive answer decides and the other process is killed.
//!
//! `RAVENCHECK_SOLVER=z3` selects z3 (one process). `RAVENCHECK_TIMEOUT` is the
//! per-goal limit in seconds (default 30; `0` = none). A goal with no definitive
//! answer in time is `Unknown`; a countermodel of AVL size can take hours to
//! find, and the counterexample file does not need one.
//! [KOR] goal의 질의를 SMT-LIB 텍스트 파일로 쓰고, 솔버를 그 파일에 대한 하위
//! 프로세스로 실행합니다. 프로세스를 직접 소유하므로 두 솔버 설정의 경주가
//! 가능합니다: 먼저 확정 답을 낸 쪽이 결정하고 나머지는 종료됩니다.

use easy_smt::{Context, ContextBuilder, SExpr};
use std::fs;
use std::io::Read;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

/// [KOR] 솔버의 답. `Unknown`은 시간 제한 안에 어느 프로세스도 확정 답을 내지 못했다는 뜻입니다.
/// [ENG] The solver's answer. `Unknown`: no process gave a definitive answer in time.
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
    pub fn solve(&self, path: &str) -> Verdict {
        fs::write(path, format!("{}(check-sat)\n", self.text))
            .unwrap_or_else(|e| panic!("Failed to write SMT query {}: {}", path, e));
        solve_file(path)
    }
}

fn solve_file(path: &str) -> Verdict {
    let solver = std::env::var("RAVENCHECK_SOLVER").unwrap_or_else(|_| "cvc5".to_string());
    let limit: u64 = std::env::var("RAVENCHECK_TIMEOUT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);

    // The solvers enforce the limit themselves; the deadline below only covers
    // one that fails to.
    let mut running: Vec<Child> = match (solver.as_str(), limit) {
        ("cvc5", 0) => ["--full-saturate-quant", "--finite-model-find"]
            .iter()
            .map(|strategy| spawn("cvc5", &["--lang", "smt2", strategy, path]))
            .collect(),
        ("cvc5", _) => ["--full-saturate-quant", "--finite-model-find"]
            .iter()
            .map(|strategy| {
                spawn("cvc5", &["--lang", "smt2", strategy, &format!("--tlimit={}", limit * 1000), path])
            })
            .collect(),
        ("z3", 0) => vec![spawn("z3", &["-smt2", path])],
        ("z3", _) => vec![spawn("z3", &["-smt2", &format!("-T:{}", limit), path])],
        (other, _) => panic!("RAVENCHECK_SOLVER must be `cvc5` or `z3`, got `{}`", other),
    };

    let deadline = (limit > 0).then(|| Instant::now() + Duration::from_secs(limit + 5));
    let mut verdict = Verdict::Unknown;
    while !running.is_empty()
        && verdict == Verdict::Unknown
        && deadline.map_or(true, |d| Instant::now() < d)
    {
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
            "Failed to start `{}` ({}); install it, or choose the solver with RAVENCHECK_SOLVER=cvc5|z3",
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
