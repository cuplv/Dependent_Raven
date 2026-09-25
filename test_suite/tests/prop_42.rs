// TIP IsaPlanner prop_42: take(S(n), Cons(x, xs)) == Cons(x, take(n, xs))
//
// One unfolding of take's S/Cons equation; no induction.
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

    #[val((n: Nat, x: Elem, xs: List) ->
        Lemma(take(Nat::S(n), List::Cons(x, xs)) == List::Cons(x, Box::new(take(n, xs)))))]
    fn tip_42(_n: Nat, _x: Elem, _xs: List) {}
}
