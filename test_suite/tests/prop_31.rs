// TIP IsaPlanner prop_31: min(min(a, b), c) == min(a, min(b, c))
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

    #[val((a: Nat, b: Nat, c: Nat) -> Lemma(min(min(a, b), c) == min(a, min(b, c))))]
    fn tip_31(a: Nat, b: Nat, c: Nat) {
        match a {
            Nat::Z => (),
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => match c {
                    Nat::Z => {
                        instantiate!(Nat::S(min(a_min, b_min)));
                        ()
                    }
                    Nat::S(c_min) => {
                        tip_31(*a_min, *b_min, *c_min);
                    }
                },
            },
        }
    }
}
