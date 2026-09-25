// TIP IsaPlanner prop_34: eq_nat(min(a, b), b) == le(b, a)
//
// Companion of prop_33 with the roles of the sides swapped. The a = Z
// branch compares eq_nat(Z, b) with le(b, Z), which needs b's shape --
// a nested case split (both sub-branches then close definitionally).
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

    #[val((a: Nat, b: Nat) -> Lemma(eq_nat(min(a, b), b) == le(b, a)))]
    #[allow(unused_variables)]
    fn tip_34(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    tip_34(*a_min, *b_min)
                }
            },
        }
    }
}
