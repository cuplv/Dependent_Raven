// TIP IsaPlanner prop_23: max(a, b) == max(b, a)
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

    #[val((a: Nat, b: Nat) -> Lemma(max(a, b) == max(b, a)))]
    fn tip_23(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    // instantiate!(Nat::S(max(a_min, b_min)));
                    // instantiate!(Nat::S(max(b_min, a_min)));
                    tip_23(*a_min, *b_min);
                }
            },
        }
    }
}
