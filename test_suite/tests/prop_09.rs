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

    // 2. Addition Function
    // We declare the signature and its refinement (the behavior of addition).
    // The macro will extract the signature to generate functionality axioms,
    // and replace this function with a relational abstraction (add_rel) in the backend.
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

    #[val((i: Nat, j: Nat, k: Nat) -> Lemma(sub(sub(i, j), k) == sub(i, add(j, k))))]
    fn tip_nine(i: Nat, j: Nat, k: Nat) {
        match i {
            Nat::Z => (),
            Nat::S(i_prime) => match j {
                Nat::Z => (),
                Nat::S(j_prime) => {
                    tip_nine(*i_prime, *j_prime, k);
                }
            },
        }
    }
}
