// TIP IsaPlanner prop_65: lt(i, S(add(m, i)))
//
// Twin of prop_18 with the sum flipped: i sits in add's SECOND argument,
// where add never recurses -- so the inductive step needs add_succ_r to
// rewrite add(m, S(i')) into S(add(m, i')) before the IH applies.
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
    fn lt(x: Nat, y: Nat) -> bool {
        match y {
            Nat::Z => false,
            Nat::S(y_min) => match x {
                Nat::Z => true,
                Nat::S(x_min) => lt(*x_min, *y_min),
            },
        }
    }

    // Helper: add(x, S(y)) == S(add(x, y)).
    #[val((x: Nat, y: Nat) -> Lemma(add(x, Nat::S(Box::new(y))) == Nat::S(Box::new(add(x, y)))))]
    fn add_succ_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                instantiate!(Nat::S(add(x_min, Nat::S(y))));
                add_succ_r(*x_min, y)
            }
        }
    }

    #[val((i: Nat, m: Nat) -> Lemma(lt(i, Nat::S(Box::new(add(m, i))))))]
    fn tip_65(i: Nat, m: Nat) {
        match i {
            Nat::Z => (),
            Nat::S(i_min) => {
                add_succ_r(m.clone(), *i_min.clone());
                tip_65(*i_min, m)
            }
        }
    }
}
