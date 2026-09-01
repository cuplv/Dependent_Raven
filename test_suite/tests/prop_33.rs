// TIP IsaPlanner prop_33: eq_nat(min(a, b), a) == le(a, b)
//
// min's Z cases return Z outright, so unlike prop_25 no reflexivity helper
// is needed: the a = Z branch is eq_nat(Z, Z) == true definitionally, and
// the mixed branch is eq_nat(Z, S(..)) == false. Only the S-S branch needs
// the wrapped min hint and the induction hypothesis.
#[ravencheck::module]
mod tip_benchmarks {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[val]
    #[recursive]
    fn min(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => Nat::Z,
            Nat::S(x_min) => match y {
                Nat::Z => Nat::Z,
                Nat::S(y_min) => Nat::S(Box::new(min(*x_min, *y_min))),
            },
        }
    }

    #[val]
    #[recursive]
    fn le(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(x_min) => match y {
                Nat::Z => false,
                Nat::S(y_min) => le(*x_min, *y_min),
            },
        }
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

    #[val((a: Nat, b: Nat) -> Lemma(eq_nat(min(a, b), a) == le(a, b)))]
    #[allow(unused_variables)]
    fn tip_33(a: Nat, b: Nat) {
        match a {
            Nat::Z => (),
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    instantiate!(Nat::S(min(a_min, b_min)));
                    tip_33(*a_min, *b_min)
                }
            },
        }
    }
}
