// TIP IsaPlanner prop_19: len(drop(n, xs)) == sub(len(xs), n)
//
// Induction on n with a case split on xs in the S step. The Z case is
// sub(len(xs), Z) == len(xs), which needs a case split on the shape of
// len(xs) because sub matches its first argument first; the S/Cons case
// closes by the induction hypothesis at (n', t).
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
    fn len(xs: List) -> Nat {
        match xs {
            List::Nil => Nat::Z,
            List::Cons(_h, t) => Nat::S(Box::new(len(*t))),
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
    fn sub(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => Nat::Z,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => sub(*x_min, *y_min),
            },
        }
    }

    #[val((n: Nat, xs: List) -> Lemma(len(drop(n, xs)) == sub(len(xs), n)))]
    fn tip_19(n: Nat, xs: List) {
        match n {
            // sub(len(xs), Z) unfolds only once len(xs) has a known shape.
            Nat::Z => match len(xs) {
                Nat::Z => (),
                Nat::S(_k) => (),
            },
            Nat::S(n_min) => match xs {
                List::Nil => (),
                List::Cons(_h, t) => {
                    tip_19(*n_min, *t);
                }
            },
        }
    }
}
