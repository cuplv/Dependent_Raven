// TIP IsaPlanner prop_60: implies(ys != Nil, last(app(xs, ys)) == last(ys))
//
// Induction on xs. In the Cons step last(Cons(h, app(t, ys))) needs the
// shape of app(t, ys): for t == Nil that is ys itself (a case split on ys,
// whose Nil arm the hypothesis rules out); otherwise app(t, ys) is a Cons
// once its inner term app(t3, ys) is named, and the induction hypothesis
// at t closes the goal.
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
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((xs: NList, ys: NList) -> Lemma(implies(ys != NList::Nil, last(app(xs, ys)) == last(ys))))]
    fn tip_60(xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(_h, t) => match *t.clone() {
                NList::Nil => match ys {
                    NList::Nil => (),
                    NList::Cons(_h2, _t2) => (),
                },
                NList::Cons(_h3, t3) => {
                    instantiate!(app(t3, ys));
                    tip_60(*t, ys);
                }
            },
        }
    }
}
