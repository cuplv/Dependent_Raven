// TIP IsaPlanner prop_07: sub(add(n, m), n) == m
//
// Lemma-gap fixture: the instantiate procedure has already run on the
// failing branch and found NOTHING to add -- the frontier is empty from
// the start (the only pinned unfolding, add at n = Z, produces no new
// terms). The verification still fails. The missing piece is proof
// structure, not a term.
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
            Nat::S(x_prime) => Nat::S(Box::new(add(*x_prime, y))),
        }
    }

    #[val]
    #[recursive]
    fn sub(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => Nat::Z,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => sub(*x_min, *y_min),
            },
        }
    }

    #[val((n: Nat, m: Nat) -> Lemma(sub(add(n, m), n) == m))]
    fn tip_seven(n: Nat, m: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_prime) => {
                instantiate!(Nat::S(add(n_prime, m)));
                tip_seven(*n_prime, m);
            }
        }
    }
}
