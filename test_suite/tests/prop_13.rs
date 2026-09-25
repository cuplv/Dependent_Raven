// TIP IsaPlanner prop_13: drop(S(n), Cons(x, xs)) == drop(n, xs)
//
// One unfolding of drop's S/Cons equation; no induction.
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

    #[val((n: Nat, x: Elem, xs: List) -> Lemma(drop(Nat::S(n), List::Cons(x, xs)) == drop(n, xs)))]
    fn tip_13(_n: Nat, _x: Elem, _xs: List) {}
}
