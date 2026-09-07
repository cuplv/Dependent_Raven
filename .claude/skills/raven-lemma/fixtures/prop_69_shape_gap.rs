// TIP IsaPlanner prop_69: le(n, add(m, n))
//
// Lemma-gap fixture: the induction hypothesis is present and the
// instantiate procedure found NOTHING to add -- the frontier is empty
// from the start (the goal's own unfolding is blocked by an opaque
// application in scrutinee position). The verification still fails.
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
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
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

    #[val((n: Nat, m: Nat) -> Lemma(le(n, add(m, n))))]
    fn tip_69(n: Nat, m: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => {
                tip_69(*n_min, m);
            }
        }
    }
}
