// TIP IsaPlanner prop_70: le(m, n) ==> le(m, S(n))
//
// An implication goal over le alone. The m = S(..), n = Z branch is
// vacuous (the antecedent le(S(..), Z) is false), and the S-S branch
// needs nothing but the induction hypothesis: the antecedent steps down
// by le's S-S equation, unlocking the IH's gate one level below.
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

    #[val((m: Nat, n: Nat) -> Lemma(implies(le(m, n), le(m, Nat::S(Box::new(n))))))]
    #[allow(unused_variables)]
    fn tip_70(m: Nat, n: Nat) {
        match m {
            Nat::Z => (),
            Nat::S(m_min) => match n {
                Nat::Z => (),
                Nat::S(n_min) => tip_70(*m_min, *n_min),
            },
        }
    }
}
