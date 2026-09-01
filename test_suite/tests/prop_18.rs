// TIP IsaPlanner prop_18: lt(i, S(add(i, m)))
//
// A bare-predicate goal (no equality): i is strictly below S(i + m).
// The S case unfolds add(i, m) to S(add(i_min, m)) -- the same wrapped-add
// hint as prop_09 -- and the induction hypothesis closes lt one level down.
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

    #[val((i: Nat, m: Nat) -> Lemma(lt(i, Nat::S(Box::new(add(i, m))))))]
    fn tip_18(i: Nat, m: Nat) {
        match i {
            Nat::Z => (),
            Nat::S(i_min) => {
                instantiate!(Nat::S(add(i_min, m)));
                tip_18(*i_min, m)
            }
        }
    }
}
