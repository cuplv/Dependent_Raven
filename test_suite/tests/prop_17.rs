// TIP IsaPlanner prop_17: le(n, Z) == eq_nat(n, Z)
//
// Purely definitional: for each shape of n, both sides collapse in one
// step (le(Z, Z) = true = eq_nat(Z, Z); le(S n', Z) = false = eq_nat(S n', Z)),
// so the case split alone discharges the proof -- no hints, no helpers.
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

    #[val((n: Nat) -> Lemma(le(n, Nat::Z) == eq_nat(n, Nat::Z)))]
    #[allow(unused_variables)]
    fn tip_17(n: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(_n_min) => (),
        }
    }
}
