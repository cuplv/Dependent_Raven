// TIP IsaPlanner prop_16: implies(xs == Nil, last(Cons(x, xs)) == x)
//
// One unfolding of last's Cons/Nil equation under the hypothesis; no
// induction.
#[ravencheck::module]
mod tip_benchmarks {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum NList {
        Nil,
        Cons(Nat, Box<NList>),
    }

    #[val]
    #[recursive]
    fn last(xs: NList) -> Nat {
        match xs {
            NList::Nil => Nat::Z,
            NList::Cons(h, t) => match *t {
                NList::Nil => h,
                NList::Cons(h2, t2) => last(NList::Cons(h2, t2)),
            },
        }
    }

    #[val((x: Nat, xs: NList) -> Lemma(implies(xs == NList::Nil, last(NList::Cons(x, xs)) == x)))]
    fn tip_16(_x: Nat, _xs: NList) {}
}
