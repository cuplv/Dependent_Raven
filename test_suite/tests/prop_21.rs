// TIP IsaPlanner prop_21: le(n, add(n, m))  --  n <= n + m
// Exercises a Bool-returning recursive function (le) used as a proposition.
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
    pub fn add(x: Nat, y: Nat) -> Nat {
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

    #[val((n: Nat, m: Nat) -> Lemma(le(n, add(n, m))))]
    fn tip_21(n: Nat, m: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => {
                tip_21(*n_min, m);
            }
        }
    }
}
