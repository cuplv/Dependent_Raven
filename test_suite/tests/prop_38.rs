// TIP IsaPlanner prop_38: count(n, app(xs, Cons(n, Nil))) == S(count(n, xs))
//
// Induction on xs. The Nil case is count(n, Cons(n, Nil)) == S(Z), which
// unfolds through the guard eq_nat(n, n) -- discharged by the eq_refl
// helper. The Cons step unfolds both sides through eq_nat(n, h) and
// closes by the induction hypothesis at t.
#[ravencheck::module]
mod tip_benchmarks {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum NList {
        Nil,
        Cons(Nat, Box<NList>),
    }

    #[val]
    #[recursive]
    fn eq_nat(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => match y {
                Nat::Z => true,
                Nat::S(_y_min) => false,
            },
            Nat::S(x_min) => match y {
                Nat::Z => false,
                Nat::S(y_min) => eq_nat(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn count(x: Nat, xs: NList) -> Nat {
        match xs {
            NList::Nil => Nat::Z,
            NList::Cons(h, t) => {
                if eq_nat(x.clone(), h) {
                    Nat::S(Box::new(count(x, *t)))
                } else {
                    count(x, *t)
                }
            }
        }
    }

    #[val]
    #[recursive]
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    // Helper: eq_nat is reflexive.
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }

    #[val((n: Nat, xs: NList) ->
        Lemma(count(n, app(xs, NList::Cons(n, Box::new(NList::Nil)))) == Nat::S(count(n, xs))))]
    fn tip_38(n: Nat, xs: NList) {
        match xs {
            NList::Nil => eq_refl(n),
            NList::Cons(h, t) => {
                // The guard of count's Cons equation at the head.
                instantiate!(eq_nat(n, h));
                tip_38(n, *t);
            }
        }
    }
}
