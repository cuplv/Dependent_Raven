// A run reports EVERY failing goal, not only the first: before this, the driver
// returned at the first counterexample, so a proof with several failing
// branches cost one full run per branch just to see them.
use std::collections::HashMap;

#[test]
fn every_failing_goal_is_reported_in_one_run() {
    let mut program = frontend::ast::Program {
        datatypes: HashMap::new(),
        functions: HashMap::new(),
        goals: Vec::new(),
    };

    frontend::api::register_enum(&mut program, "Nat", "enum Nat { Z, S(Box<Nat>) }");

    // FALSE.
    frontend::api::register_val(
        &mut program,
        "all_zero",
        Some("(x: Nat) -> Lemma(x == Nat::Z)"),
        "fn all_zero(x: Nat) { () }",
        false,
    );
    // True; sits between the two failures and must not be reported.
    frontend::api::register_val(
        &mut program,
        "refl",
        Some("(x: Nat) -> Lemma(x == x)"),
        "fn refl(x: Nat) { () }",
        false,
    );
    // FALSE.
    frontend::api::register_val(
        &mut program,
        "all_equal",
        Some("(x: Nat, y: Nat) -> Lemma(x == y)"),
        "fn all_equal(x: Nat, y: Nat) { () }",
        false,
    );

    let report = backend::smt::encode_and_solve(program).expect_err("two goals are false");
    assert!(report.contains("'all_zero_vc_1'"), "first failure missing:\n{}", report);
    assert!(report.contains("'all_equal_vc_1'"), "second failure missing:\n{}", report);
    assert!(!report.contains("'refl_vc_1'"), "a verified goal was reported:\n{}", report);
}
