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

    #[val((a: Nat, b: Nat, c: Nat) -> Lemma(sub(sub(Nat::S(a), b), Nat::S(c)) == sub(sub(a,b), c)))]
    fn tip_79(a: Nat, b: Nat, c: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(b_prime) => {
                    instantiate!(sub(Nat::Z, b_prime));
                    ()
                }
            },
            Nat::S(a_prime) => match b {
                Nat::Z => (),
                Nat::S(b_prime) => {
                    tip_79(*a_prime, *b_prime, c);
                }
            },
        }
    }
}
