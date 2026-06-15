// TIP Benchmark Example
// A classic example: Proving the commutativity of natural number addition
// using F* style refinement types and uncurried signatures.
#[ravencheck::module]
mod tip_benchmarks {

    // 1. Inductive Datatype Definition for Natural Numbers
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

    #[val((n: Nat, m: Nat) -> Lemma(sub(add(n,m), n) == m))]
    fn tip_seven(n: Nat, m: Nat) {
        match n {
            Nat::Z => {
                instantiate!(sub(m, n));
                match m {
                    Nat::Z => (),
                    Nat::S(m_prime) => (),
                }
            }
            Nat::S(n_prime) => {
                instantiate!(Nat::S(add(n_prime, m)));
                tip_seven(*n_prime, m);
            }
        }
    }
}
