// TIP IsaPlanner prop_29: elem(x, ins1(x, xs))
//
// Induction on xs. The two cases show the two faces of a guard: in the
// Nil case elem unfolds through eq_nat(x, x), which must HOLD (helper
// eq_refl); in the Cons case ins1 and elem unfold through eq_nat(x, h),
// which only has to EXIST (a hint) since both outcomes close, the second
// by the induction hypothesis.
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

    // Insert x unless it is already present (TIP's ins1).
    #[val]
    #[recursive]
    fn ins1(x: Nat, xs: NList) -> NList {
        match xs {
            NList::Nil => NList::Cons(x, Box::new(NList::Nil)),
            NList::Cons(h, t) => {
                if eq_nat(x.clone(), h.clone()) {
                    NList::Cons(h, t)
                } else {
                    NList::Cons(h, Box::new(ins1(x, *t)))
                }
            }
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

    #[val((x: Nat, xs: NList) -> Lemma(elem(x, ins1(x, xs))))]
    fn tip_29(x: Nat, xs: NList) {
        match xs {
            // elem(x, Cons(x, Nil)) unfolds through eq_nat(x, x), which must
            // hold, not merely be defined.
            NList::Nil => eq_refl(x),
            NList::Cons(h, t) => {
                // The guard shared by ins1's and elem's Cons equations; both
                // outcomes close, so naming it is enough.
                instantiate!(eq_nat(x, h));
                tip_29(x, *t);
            }
        }
    }
}
