// TIP IsaPlanner prop_22: max(max(a, b), c) == max(a, max(b, c))
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

    #[val((a: Nat, b: Nat, c: Nat) -> Lemma(max(max(a, b), c) == max(a, max(b, c))))]
    fn tip_22(a: Nat, b: Nat, c: Nat) {
        match a {
            Nat::Z => (),
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => match c {
                    Nat::Z => {
                        instantiate!(Nat::S(max(a_min, b_min)));
                        ()
                    }
                    Nat::S(c_min) => {
                        instantiate!(Nat::S(max(a_min, b_min)));
                        instantiate!(Nat::S(max(b_min, c_min)));
                        instantiate!(Nat::S(max(max(a_min, b_min), c_min)));
                        instantiate!(Nat::S(max(a_min, max(b_min, c_min))));
                        tip_22(*a_min, *b_min, *c_min);
                    }
                },
            },
        }
    }
}
