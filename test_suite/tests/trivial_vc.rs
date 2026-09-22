// A subtyping obligation whose expected refinement is literally `true` is valid
// whatever the context says (`Γ ⇒ true`), so no goal is generated for it.
// Such obligations arise for every argument of a call whose parameter type
// carries no refinement -- most calls in a proof body -- and made up 97 % of
// the AVL proof's goals before this. A `requires` clause on a parameter is a
// real obligation and must still be generated (and can still fail).
use std::collections::HashMap;

fn program_with_calls(pre_holds: bool) -> frontend::ast::Program {
    let mut program = frontend::ast::Program {
        datatypes: HashMap::new(),
        functions: HashMap::new(),
        goals: Vec::new(),
    };
    frontend::api::register_enum(&mut program, "Nat", "enum Nat { Z, S(Box<Nat>) }");

    frontend::api::register_val(
        &mut program,
        "is_zero",
        None,
        "fn is_zero(n: Nat) -> bool { match n { Nat::Z => true, Nat::S(_) => false } }",
        false,
    );

    // Unrefined parameters: calling it costs no obligation.
    frontend::api::register_val(
        &mut program,
        "refl",
        Some("(a: Nat, b: Nat) -> Lemma(a == a)"),
        "fn refl(a: Nat, b: Nat) { () }",
        false,
    );

    // A precondition: calling it costs one obligation.
    frontend::api::register_val(
        &mut program,
        "needs_zero",
        Some("(n: Nat) -> Lemma(requires(is_zero(n)), ensures(n == Nat::Z))"),
        "fn needs_zero(n: Nat) { match n { Nat::Z => (), Nat::S(m) => () } }",
        false,
    );

    // The precondition holds only in the Z branch; `pre_holds` selects whether
    // needs_zero is called there or in the S branch.
    let body = if pre_holds {
        "fn user(x: Nat) { match x { Nat::Z => { instantiate!(is_zero(x)); refl(x.clone(), x.clone()); needs_zero(x); } Nat::S(m) => () } }"
    } else {
        "fn user(x: Nat) { match x { Nat::Z => (), Nat::S(m) => { refl(x.clone(), x.clone()); needs_zero(x); } } }"
    };
    // Distinct lemma names per case: the two tests run in parallel and share logs/.
    let name = if pre_holds { "user_ok" } else { "user_bad" };
    let body = body.replace("fn user(", &format!("fn {}(", name));
    frontend::api::register_val(&mut program, name, Some("(x: Nat) -> Lemma(x == x)"), &body, false);
    program
}

#[test]
fn unrefined_arguments_generate_no_goals() {
    let program = program_with_calls(true);
    let names: Vec<&str> = program.goals.iter().map(|g| g.name.as_str()).collect();
    // refl's own postcondition, needs_zero's two arms, and in `user`: the
    // precondition of needs_zero plus user's postcondition in each arm.
    // Nothing for refl's two arguments.
    assert_eq!(
        names,
        vec!["refl_vc_1", "needs_zero_vc_1", "needs_zero_vc_2", "user_ok_vc_1", "user_ok_vc_2", "user_ok_vc_3"],
        "unexpected goals: {:?}",
        names
    );
    backend::smt::encode_and_solve(program).expect("all goals are valid");
}

#[test]
fn precondition_obligation_is_still_checked() {
    let program = program_with_calls(false);
    let report = backend::smt::encode_and_solve(program).expect_err("is_zero(x) is not provable");
    // Z arm: postcondition only (vc_1); S arm: the precondition (vc_2), then the postcondition.
    assert!(report.contains("'user_bad_vc_2'"), "precondition failure missing:\n{}", report);
    assert!(!report.contains("'user_bad_vc_1'"), "the Z arm has no obligation to fail:\n{}", report);
}
