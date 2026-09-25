// TIP IsaPlanner prop_81: take(n, drop(m, xs)) == drop(m, take(add(n, m), xs))
//
// Induction on m (n stays general) with a case split on xs; the twin of
// prop_56. add recurses on its first argument, so add_zero (m == Z) and
// add_succ (S cases) supply the facts about its second; take_nil handles
// take of Nil with a variable count in the S/Nil case.
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
    fn take(n: Nat, xs: List) -> List {
        match n {
            Nat::Z => List::Nil,
            Nat::S(n_min) => match xs {
                List::Nil => List::Nil,
                List::Cons(h, t) => List::Cons(h, Box::new(take(*n_min, *t))),
            },
        }
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

    // Helper: take of Nil is Nil, whatever the count.
    #[val((k: Nat) -> Lemma(take(k, List::Nil) == List::Nil))]
    fn take_nil(k: Nat) {
        match k {
            Nat::Z => (),
            Nat::S(_k_min) => (),
        }
    }

    #[val((n: Nat, m: Nat, xs: List) -> Lemma(take(n, drop(m, xs)) == drop(m, take(add(n, m), xs))))]
    fn tip_81(n: Nat, m: Nat, xs: List) {
        match m {
            Nat::Z => add_zero(n),
            Nat::S(m_min) => match xs {
                List::Nil => {
                    take_nil(n.clone());
                    add_succ(n.clone(), *m_min.clone());
                    take_nil(Nat::S(Box::new(add(n, *m_min))));
                }
                List::Cons(_h, t) => {
                    add_succ(n.clone(), *m_min.clone());
                    tip_81(n, *m_min, *t);
                }
            },
        }
    }
}
