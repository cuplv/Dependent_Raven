// TIP IsaPlanner prop_40: take(Z, xs) == Nil
//
// One unfolding of take's Z equation; no induction.
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

    #[val((xs: List) -> Lemma(take(Nat::Z, xs) == List::Nil))]
    fn tip_40(_xs: List) {}
}
