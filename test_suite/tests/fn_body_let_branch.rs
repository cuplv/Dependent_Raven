// `let` in a FUNCTION body followed by a branch. Each binding becomes a
// universally quantified binder plus the guard `x == e` in the definitional
// axioms, so the body may `match` on a let-bound call result and an `if` may
// follow several `let`s (the shape of AVL's `balance`). Previously any `let`
// before `if`/`match` in a function body panicked in ANF.
#[ravencheck::module]
mod fn_body_let_branch {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[val]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
        }
    }

    #[val]
    fn is_zero(n: Nat) -> bool {
        match n {
            Nat::Z => true,
            Nat::S(_) => false,
        }
    }

    // let binding a CALL, used at the tail.
    #[val]
    fn succ_of_sum(x: Nat, y: Nat) -> Nat {
        let s = add(x, y);
        Nat::S(Box::new(s))
    }

    // let binding a call, then MATCH on the bound name.
    #[val]
    fn sum_or_bump(x: Nat, y: Nat) -> Nat {
        let s = add(x, y);
        match s {
            Nat::Z => Nat::Z,
            Nat::S(p) => Nat::S(Box::new(Nat::S(p))),
        }
    }

    // two lets, then an IF chain (the `balance` shape).
    #[val]
    fn pick(x: Nat, y: Nat) -> Nat {
        let a = add(x.clone(), y.clone());
        let b = add(y, x);
        if is_zero(a.clone()) {
            b
        } else {
            a
        }
    }

    // As with any call inside a definition, a let-bound call needs a definedness
    // witness before its equation fires; the hints below supply them.
    #[val((y: Nat) -> Lemma(succ_of_sum(Nat::Z, y) == Nat::S(Box::new(y))))]
    fn succ_of_sum_z(y: Nat) {
        instantiate!(add(Nat::Z, y));
    }

    #[val((n: Nat) -> Lemma(sum_or_bump(Nat::Z, Nat::Z) == Nat::Z))]
    fn sum_or_bump_zz(n: Nat) {
        instantiate!(add(Nat::Z, Nat::Z));
    }

    #[val((x: Nat, y: Nat) -> Lemma(sum_or_bump(Nat::S(Box::new(x)), y) == Nat::S(Box::new(Nat::S(Box::new(add(x, y)))))))]
    fn sum_or_bump_s(x: Nat, y: Nat) {
        instantiate!(add(Nat::S(x), y));
        instantiate!(Nat::S(add(x, y)));
    }

    #[val((n: Nat) -> Lemma(pick(Nat::Z, Nat::Z) == Nat::Z))]
    fn pick_zz(n: Nat) {
        instantiate!(add(Nat::Z, Nat::Z));
        instantiate!(is_zero(add(Nat::Z, Nat::Z)));
    }

    // The else branch never uses `b`, and no witness for add(y, S(x)) is given:
    // a let that is not matched on is substituted, so it costs nothing where unused.
    #[val((x: Nat, y: Nat) -> Lemma(pick(Nat::S(Box::new(x)), y) == add(Nat::S(Box::new(x)), y)))]
    fn pick_s(x: Nat, y: Nat) {
        instantiate!(Nat::S(add(x, y)));
        instantiate!(is_zero(add(Nat::S(x), y)));
    }
}
