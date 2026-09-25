// TIP IsaPlanner prop_69: le(n, add(m, n))
//
// Same skeleton as prop_65 with le in place of lt: n sits in add's second
// argument, so the inductive case rewrites add(m, S(n')) via add_succ_r
// and le's S-S equation steps down to the induction hypothesis.
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

    // Helper: add(x, S(y)) == S(add(x, y)).
    #[val((x: Nat, y: Nat) -> Lemma(add(x, Nat::S(Box::new(y))) == Nat::S(Box::new(add(x, y)))))]
    fn add_succ_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                add_succ_r(*x_min, y)
            }
        }
    }

    #[val((n: Nat, m: Nat) -> Lemma(le(n, add(m, n))))]
    fn tip_69(n: Nat, m: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => {
                add_succ_r(m.clone(), *n_min.clone());
                tip_69(*n_min, m)
            }
        }
    }
}
