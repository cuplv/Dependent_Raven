// TIP IsaPlanner prop_11: drop(Z, xs) == xs
//
// One unfolding of drop's Z equation; no induction.
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

    #[val((xs: List) -> Lemma(drop(Nat::Z, xs) == xs))]
    fn tip_11(_xs: List) {}
}
