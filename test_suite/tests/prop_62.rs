// TIP IsaPlanner prop_62: implies(xs != Nil, last(Cons(x, xs)) == last(xs))
//
// No induction: a case split on xs (the hypothesis rules out Nil) lets
// last's Cons/Cons equation unfold on the left.
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

    #[val((xs: NList, x: Nat) -> Lemma(implies(xs != NList::Nil, last(NList::Cons(x, xs)) == last(xs))))]
    fn tip_62(xs: NList, _x: Nat) {
        match xs {
            NList::Nil => (),
            NList::Cons(_h, _t) => (),
        }
    }
}
