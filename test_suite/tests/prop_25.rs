// TIP IsaPlanner prop_25: eq_nat(max(a, b), b) == le(a, b)
//
// Mirror image of prop_24 (which relates max(a, b) == a to le(b, a)).
// The a = Z branch reduces to eq_nat(b, b) == true, discharged by eq_refl;
// the S-S branch needs the wrapped max hint and the induction hypothesis.
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
    fn max(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => y,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => Nat::S(Box::new(max(*x_min, *y_min))),
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

    // Helper: eq_nat is reflexive (the a = Z branch reduces to eq_nat(b, b)).
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }

    #[val((a: Nat, b: Nat) -> Lemma(eq_nat(max(a, b), b) == le(a, b)))]
    fn tip_25(a: Nat, b: Nat) {
        match a {
            Nat::Z => eq_refl(b),
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    instantiate!(Nat::S(max(a_min, b_min)));
                    tip_25(*a_min, *b_min)
                }
            },
        }
    }
}
