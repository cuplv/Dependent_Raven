// TIP IsaPlanner prop_28: elem(x, app(xs, Cons(x, Nil)))
//
// Induction on xs. The Nil case is elem(x, Cons(x, Nil)), which unfolds
// through the guard eq_nat(x, x) -- discharged by the eq_refl helper. The
// Cons step unfolds through eq_nat(x, h) and closes by the induction
// hypothesis at t.
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
    fn elem(x: Nat, xs: NList) -> bool {
        match xs {
            NList::Nil => false,
            NList::Cons(h, t) => {
                if eq_nat(x.clone(), h) {
                    true
                } else {
                    elem(x, *t)
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

    #[val((x: Nat, xs: NList) -> Lemma(elem(x, app(xs, NList::Cons(x, Box::new(NList::Nil))))))]
    fn tip_28(x: Nat, xs: NList) {
        match xs {
            NList::Nil => eq_refl(x),
            NList::Cons(h, t) => {
                // The guard of elem's Cons equation at the head.
                instantiate!(eq_nat(x, h));
                tip_28(x, *t);
            }
        }
    }
}
