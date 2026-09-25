// TIP IsaPlanner prop_01: app(take(n, xs), drop(n, xs)) == xs
//
// Induction on n with a case split on xs in the S step. The Z case is
// pure unfolding (take(Z, xs) = Nil, drop(Z, xs) = xs, app(Nil, xs) = xs);
// the S/Cons case rewrites both sides to Cons(h, _) and closes by the
// induction hypothesis at (n', t).
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
    fn app(x: List, y: List) -> List {
        match x {
            List::Nil => y,
            List::Cons(h, t) => List::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((n: Nat, xs: List) -> Lemma(app(take(n, xs), drop(n, xs)) == xs))]
    fn tip_01(n: Nat, xs: List) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => match xs {
                List::Nil => (),
                List::Cons(_h, t) => {
                    tip_01(*n_min, *t);
                }
            },
        }
    }
}
