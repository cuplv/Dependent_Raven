// TIP IsaPlanner prop_56: drop(n, drop(m, xs)) == drop(add(n, m), xs)
//
// Induction on m (n stays general) with a case split on xs. add recurses
// on its first argument, so every step needs a fact about its second:
// add_zero in the m == Z case, add_succ in the S cases; drop_nil handles
// drop(n, Nil) with a variable count in the S/Nil case.
#[ravencheck::module]
mod tip_benchmarks {

    // Uninterpreted element sort (the benchmark is polymorphic in `a`).
    #[declare]
    type Elem = u32;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum List {
        Nil,
        Cons(Elem, Box<List>),
    }

    #[val]
    #[recursive]
    fn drop(n: Nat, xs: List) -> List {
        match n {
            Nat::Z => xs,
            Nat::S(n_min) => match xs {
                List::Nil => List::Nil,
                List::Cons(_h, t) => drop(*n_min, *t),
            },
        }
    }

    #[val]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
        }
    }

    // Helper: Z is a right identity of add.
    #[val((n: Nat) -> Lemma(add(n, Nat::Z) == n))]
    fn add_zero(n: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => add_zero(*n_min),
        }
    }

    // Helper: a successor on the right of add moves outside.
    #[val((n: Nat, m: Nat) -> Lemma(add(n, Nat::S(m)) == Nat::S(add(n, m))))]
    fn add_succ(n: Nat, m: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => add_succ(*n_min, m),
        }
    }

    // Helper: drop of Nil is Nil, whatever the count.
    #[val((k: Nat) -> Lemma(drop(k, List::Nil) == List::Nil))]
    fn drop_nil(k: Nat) {
        match k {
            Nat::Z => (),
            Nat::S(_k_min) => (),
        }
    }

    #[val((n: Nat, m: Nat, xs: List) -> Lemma(drop(n, drop(m, xs)) == drop(add(n, m), xs)))]
    fn tip_56(n: Nat, m: Nat, xs: List) {
        match m {
            // drop(n, xs) == drop(add(n, Z), xs).
            Nat::Z => add_zero(n),
            Nat::S(m_min) => match xs {
                // Both sides drop a variable count from Nil.
                List::Nil => {
                    drop_nil(n.clone());
                    add_succ(n, *m_min);
                }
                // drop(add(n, S(m')), Cons(h, t)) steps once more than
                // drop(add(n, m'), t) only after the S moves outside.
                List::Cons(_h, t) => {
                    add_succ(n.clone(), *m_min.clone());
                    tip_56(n, *m_min, *t);
                }
            },
        }
    }
}
