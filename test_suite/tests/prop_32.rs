// TIP IsaPlanner prop_32: min(a, b) == min(b, a)
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

    #[val((a: Nat, b: Nat) -> Lemma(min(a, b) == min(b, a)))]
    fn tip_32(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    instantiate!(Nat::S(min(a_min, b_min)));
                    instantiate!(Nat::S(min(b_min, a_min)));
                    tip_32(*a_min, *b_min);
                }
            },
        }
    }
}
