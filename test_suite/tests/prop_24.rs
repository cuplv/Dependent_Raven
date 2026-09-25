// TIP IsaPlanner prop_24: (max(a, b) == a) <=> (b <= a)
// Exercises Bool-valued equality between two Bool-returning recursive functions,
// plus a helper lemma (eq_refl) called in tail position of one branch.
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

    // Helper: eq_nat is reflexive. Needed for the a = S(_), b = Z branch,
    // where the goal reduces to eq_nat(a, a) == true.
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }

    #[val((a: Nat, b: Nat) -> Lemma(eq_nat(max(a, b), a) == le(b, a)))]
    fn tip_24(a: Nat, b: Nat) {
        match a.clone() {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => eq_refl(a),
                Nat::S(b_min) => {
                    tip_24(*a_min, *b_min);
                }
            },
        }
    }
}
