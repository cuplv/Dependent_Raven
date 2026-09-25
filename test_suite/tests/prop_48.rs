// TIP IsaPlanner prop_48: implies(xs != Nil, app(butlast(xs), Cons(last(xs), Nil)) == xs)
//
// Induction on xs with a case split on t (butlast and last both need the
// first two elements). For t == Nil both sides are Cons(h, Nil); otherwise
// butlast(xs) == Cons(h, butlast(t)), last(xs) == last(t), and the
// induction hypothesis at t (which is not Nil) closes the goal.
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

    #[val]
    #[recursive]
    fn butlast(xs: NList) -> NList {
        match xs {
            NList::Nil => NList::Nil,
            NList::Cons(h, t) => match *t {
                NList::Nil => NList::Nil,
                NList::Cons(h2, t2) => NList::Cons(h, Box::new(butlast(NList::Cons(h2, t2)))),
            },
        }
    }

    #[val]
    #[recursive]
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((xs: NList) -> Lemma(implies(xs != NList::Nil, app(butlast(xs), NList::Cons(last(xs), Box::new(NList::Nil))) == xs)))]
    fn tip_48(xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(_h, t) => match *t.clone() {
                NList::Nil => (),
                NList::Cons(_h2, _t2) => {
                    tip_48(*t);
                }
            },
        }
    }
}
