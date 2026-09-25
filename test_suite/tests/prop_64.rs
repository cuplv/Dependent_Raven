// TIP IsaPlanner prop_64: last(app(xs, Cons(x, Nil))) == x
//
// Induction on xs. In the Cons step last(Cons(h, app(t, [x]))) unfolds
// only once app(t, [x]) has a known shape, so the step splits on t: for
// t == Nil it is last(Cons(h, Cons(x, Nil))) == x; otherwise app(t, [x])
// is a Cons, last recurses into it, and the induction hypothesis at t
// closes the goal.
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

    #[val((x: Nat, xs: NList) -> Lemma(last(app(xs, NList::Cons(x, Box::new(NList::Nil)))) == x))]
    fn tip_64(x: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(_h, t) => match *t.clone() {
                NList::Nil => (),
                NList::Cons(_h2, t2) => {
                    // Inner term: app(t, [x]) unfolds to Cons(h2, app(t2, [x])).
                    instantiate!(app(t2, NList::Cons(x, NList::Nil)));
                    tip_64(x, *t);
                }
            },
        }
    }
}
