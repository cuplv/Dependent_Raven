// A goal the solver cannot decide within the time limit is reported as
// UNKNOWN, the run continues to the next goal, and the counterexample file is
// still written: it is built from the goal and its instantiation list (the
// ledger), never from a solver model, so the frontier procedure can work on
// it. Its header says `; verdict: unknown` so a reader knows no countermodel
// was found.
//
// The fixture is the AVL `balance_left` helper as a proof session left it:
// no guard-term hints for `balance`'s equations (so unprovable), and a dozen
// helper-lemma calls per branch whose instantiated facts and witnesses make
// the countermodel large enough that the model finder does not find it in
// the 3-second limit set here. (Without the helper calls the same goal gets
// its countermodel in under a second; the session waited over twenty minutes
// with them.)
use std::collections::HashMap;

fn avl_program() -> frontend::ast::Program {
    let mut program = frontend::ast::Program {
        datatypes: HashMap::new(),
        functions: HashMap::new(),
        goals: Vec::new(),
    };
    frontend::api::register_enum(&mut program, "Nat", "enum Nat { Z, S(Box<Nat>) }");
    frontend::api::register_enum(&mut program, "Tree", "enum Tree { Leaf, Node(Box<Tree>, Nat, Nat, Box<Tree>) }");
    frontend::api::register_val(&mut program, "leq", None, "fn leq(x: Nat, y: Nat) -> bool {\n    match x {\n        Nat::Z => true,\n        Nat::S(x1) => match y {\n            Nat::Z => false,\n            Nat::S(y1) => leq(*x1, *y1),\n        },\n    }\n}", true);
    frontend::api::register_val(&mut program, "eq_nat", None, "fn eq_nat(x: Nat, y: Nat) -> bool {\n    match x {\n        Nat::Z => match y {\n            Nat::Z => true,\n            Nat::S(_) => false,\n        },\n        Nat::S(x1) => match y {\n            Nat::Z => false,\n            Nat::S(y1) => eq_nat(*x1, *y1),\n        },\n    }\n}", true);
    frontend::api::register_val(&mut program, "max", None, "fn max(x: Nat, y: Nat) -> Nat {\n    match x {\n        Nat::Z => y,\n        Nat::S(x1) => match y {\n            Nat::Z => Nat::S(x1),\n            Nat::S(y1) => Nat::S(Box::new(max(*x1, *y1))),\n        },\n    }\n}", true);
    frontend::api::register_val(&mut program, "height", None, "fn height(t: Tree) -> Nat {\n    match t {\n        Tree::Leaf => Nat::Z,\n        Tree::Node(_, _, h, _) => h,\n    }\n}", false);
    frontend::api::register_val(&mut program, "node", None, "fn node(l: Tree, v: Nat, r: Tree) -> Tree {\n    Tree::Node(\n        Box::new(l.clone()),\n        v,\n        Nat::S(Box::new(max(height(l), height(r.clone())))),\n        Box::new(r),\n    )\n}", false);
    frontend::api::register_val(&mut program, "is_balanced", None, "fn is_balanced(t: Tree) -> bool {\n    match t {\n        Tree::Leaf => true,\n        Tree::Node(l, _, h, r) => {\n            let hl = height(*l.clone());\n            let hr = height(*r.clone());\n            leq(hl.clone(), Nat::S(Box::new(hr.clone())))\n                && leq(hr.clone(), Nat::S(Box::new(hl.clone())))\n                && eq_nat(h, Nat::S(Box::new(max(hl, hr))))\n                && is_balanced(*l)\n                && is_balanced(*r)\n        }\n    }\n}", true);
    frontend::api::register_val(&mut program, "rotate_right", None, "fn rotate_right(l: Tree, v: Nat, r: Tree) -> Tree {\n    match l {\n        Tree::Node(ll, lv, _, lr) => {\n            if leq(height(*lr.clone()), height(*ll.clone())) {\n                node(*ll, lv, node(*lr, v, r))\n            } else {\n                match *lr {\n                    Tree::Node(lrl, lrv, _, lrr) => {\n                        node(node(*ll, lv, *lrl), lrv, node(*lrr, v, r))\n                    }\n                    Tree::Leaf => Tree::Leaf,\n                }\n            }\n        }\n        Tree::Leaf => Tree::Leaf,\n    }\n}", false);
    frontend::api::register_val(&mut program, "rotate_left", None, "fn rotate_left(l: Tree, v: Nat, r: Tree) -> Tree {\n    match r {\n        Tree::Node(rl, rv, _, rr) => {\n            if leq(height(*rl.clone()), height(*rr.clone())) {\n                node(node(l, v, *rl), rv, *rr)\n            } else {\n                match *rl {\n                    Tree::Node(rll, rlv, _, rlr) => {\n                        node(node(l, v, *rll), rlv, node(*rlr, rv, *rr))\n                    }\n                    Tree::Leaf => Tree::Leaf,\n                }\n            }\n        }\n        Tree::Leaf => Tree::Leaf,\n    }\n}", false);
    frontend::api::register_val(&mut program, "balance", None, "fn balance(l: Tree, v: Nat, r: Tree) -> Tree {\n    let hl = height(l.clone());\n    let hr = height(r.clone());\n    if leq(Nat::S(Box::new(Nat::S(Box::new(hr.clone())))), hl.clone()) {\n        rotate_right(l, v, r)\n    } else if leq(Nat::S(Box::new(Nat::S(Box::new(hl)))), hr) {\n        rotate_left(l, v, r)\n    } else {\n        node(l, v, r)\n    }\n}", false);
    frontend::api::register_val(&mut program, "eq_nat_eq", Some("(a: Nat, b: Nat) -> Lemma(implies(eq_nat(a, b), a == b))"), "fn eq_nat_eq(a: Nat, b: Nat) {\n    match a {\n        Nat::Z => match b {\n            Nat::Z => (),\n            Nat::S(_b1) => (),\n        },\n        Nat::S(a1) => match b {\n            Nat::Z => (),\n            Nat::S(b1) => eq_nat_eq(*a1, *b1),\n        },\n    }\n}", true);
    frontend::api::register_val(&mut program, "eq_nat_refl", Some("(a: Nat) -> Lemma(eq_nat(a, a))"), "fn eq_nat_refl(a: Nat) {\n    match a {\n        Nat::Z => (),\n        Nat::S(a1) => eq_nat_refl(*a1),\n    }\n}", true);
    frontend::api::register_val(&mut program, "near", Some("(a: Nat, b: Nat) -> Lemma(implies( leq(a, Nat::S(Box::new(b))) && leq(b, Nat::S(Box::new(a))), a == b || a == Nat::S(Box::new(b)) || b == Nat::S(Box::new(a))))"), "fn near(a: Nat, b: Nat) {\n    match a {\n        Nat::Z => match b {\n            Nat::Z => (),\n            Nat::S(b1) => match *b1.clone() {\n                Nat::Z => (),\n                Nat::S(_b2) => (),\n            },\n        },\n        Nat::S(a1) => match b {\n            Nat::Z => match *a1.clone() {\n                Nat::Z => (),\n                Nat::S(_a2) => (),\n            },\n            Nat::S(b1) => near(*a1, *b1),\n        },\n    }\n}", true);
    frontend::api::register_val(&mut program, "nat_facts", Some("(n: Nat) -> Lemma( leq(n, n) && leq(n, Nat::S(Box::new(n))) && leq(n, Nat::S(Box::new(Nat::S(Box::new(n))))) && !leq(Nat::S(Box::new(n)), n) && !leq(Nat::S(Box::new(Nat::S(Box::new(n)))), n) && !leq(Nat::S(Box::new(Nat::S(Box::new(Nat::S(Box::new(n)))))), n) && max(n, n) == n && max(Nat::S(Box::new(n)), n) == Nat::S(Box::new(n)) && max(n, Nat::S(Box::new(n))) == Nat::S(Box::new(n)) && max(Nat::S(Box::new(Nat::S(Box::new(n)))), n) == Nat::S(Box::new(Nat::S(Box::new(n)))) && max(n, Nat::S(Box::new(Nat::S(Box::new(n))))) == Nat::S(Box::new(Nat::S(Box::new(n)))))"), "fn nat_facts(n: Nat) {\n    match n {\n        Nat::Z => (),\n        Nat::S(m) => nat_facts(*m),\n    }\n}", true);
    frontend::api::register_val(&mut program, "balance_left", Some("(l: Tree, lp: Tree, v: Nat, h: Nat, r: Tree) -> Lemma(implies( is_balanced(Tree::Node(Box::new(l), v, h, Box::new(r))) && is_balanced(lp) && (height(lp) == height(l) || height(lp) == Nat::S(Box::new(height(l)))), is_balanced(balance(lp, v, r)) && (height(balance(lp, v, r)) == h || height(balance(lp, v, r)) == Nat::S(Box::new(h)))))"), "fn balance_left(l: Tree, lp: Tree, v: Nat, h: Nat, r: Tree) {\n    eq_nat_eq(h.clone(), Nat::S(Box::new(max(height(l.clone()), height(r.clone())))));\n    near(height(l.clone()), height(r.clone()));\n    nat_facts(height(l.clone()));\n    nat_facts(height(r.clone()));\n    eq_nat_refl(Nat::S(Box::new(max(height(lp.clone()), height(r.clone())))));\n    match lp {\n        Tree::Leaf => (),\n        Tree::Node(ll, lv, hc, lr) => {\n            eq_nat_eq(hc.clone(), Nat::S(Box::new(max(height(*ll.clone()), height(*lr.clone())))));\n            near(height(*ll.clone()), height(*lr.clone()));\n            nat_facts(height(*ll.clone()));\n            nat_facts(height(*lr.clone()));\n            eq_nat_refl(Nat::S(Box::new(max(height(*lr.clone()), height(r.clone())))));\n            eq_nat_refl(Nat::S(Box::new(max(\n                height(*ll.clone()),\n                height(node(*lr.clone(), v.clone(), r.clone()))))));\n            match *lr.clone() {\n                Tree::Leaf => (),\n                Tree::Node(lrl, lrv, he, lrr) => {\n                    eq_nat_eq(he.clone(), Nat::S(Box::new(max(height(*lrl.clone()), height(*lrr.clone())))));\n                    near(height(*lrl.clone()), height(*lrr.clone()));\n                    nat_facts(height(*lrl.clone()));\n                    nat_facts(height(*lrr.clone()));\n                    eq_nat_refl(Nat::S(Box::new(max(height(*ll.clone()), height(*lrl.clone())))));\n                    eq_nat_refl(Nat::S(Box::new(max(height(*lrr.clone()), height(r.clone())))));\n                    eq_nat_refl(Nat::S(Box::new(max(\n                        height(node(*ll.clone(), lv.clone(), *lrl.clone())),\n                        height(node(*lrr.clone(), v.clone(), r.clone()))))));\n                    let _ = lrv;\n                }\n            }\n        }\n    }\n}", false);
    // A goal after the slow one: the run must reach it.
    frontend::api::register_val(&mut program, "after", Some("(n: Nat) -> Lemma(n == n)"), "fn after(n: Nat) { () }", false);
    program
}

#[test]
fn unknown_goal_is_reported_and_gets_a_counterexample_file() {
    std::env::set_var("RAVENCHECK_TIMEOUT", "3");
    let report = backend::smt::encode_and_solve(avl_program()).expect_err("balance_left is unprovable");
    std::env::remove_var("RAVENCHECK_TIMEOUT");

    assert!(report.contains("UNKNOWN"), "expected an UNKNOWN goal:\n{}", report);
    assert!(report.contains("'balance_left_vc_"), "{}", report);
    assert!(!report.contains("'after_vc_1'"), "the run did not continue past the UNKNOWN goals:\n{}", report);

    let unknown_goal = report
        .lines()
        .find_map(|l| l.strip_prefix("Verification of '").and_then(|s| s.split('\'').next()))
        .map(str::to_string)
        .expect("an UNKNOWN goal name in the report");
    let cex = std::fs::read_to_string(format!("logs/{}_counterexample.smt2", unknown_goal))
        .expect("counterexample file written for the UNKNOWN goal");
    assert!(cex.contains("; verdict: unknown"), "header lacks the verdict line:\n{}", cex);
    assert!(cex.contains("; definitions:") && cex.contains("; branch : lp = Node("), "file lacks the usual sections:\n{}", cex);
}
