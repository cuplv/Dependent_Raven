// TIP IsaPlanner prop_61: last(app(xs, ys)) == last_of_two(xs, ys)
//
// Induction on xs with a case split on ys (last_of_two matches on ys). The
// ys == Nil branch is the app_nil helper; the ys == Cons branch needs the
// shape of app(t, ys) -- a case split on t -- and, below it, the inner term
// app(t3, ys) that app's Cons equation builds, before the induction
// hypothesis at t applies.
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

    // TIP's lastOfTwo (non-recursive).
    #[val]
    fn last_of_two(xs: NList, ys: NList) -> Nat {
        match ys {
            NList::Nil => last(xs),
            NList::Cons(h, t) => last(NList::Cons(h, t)),
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

    // Helper: Nil is a right identity of app.
    #[val((xs: NList) -> Lemma(app(xs, NList::Nil) == xs))]
    fn app_nil(xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(_h, t) => app_nil(*t),
        }
    }

    #[val((xs: NList, ys: NList) -> Lemma(last(app(xs, ys)) == last_of_two(xs, ys)))]
    fn tip_61(xs: NList, ys: NList) {
        match xs {
            // last_of_two matches on ys.
            NList::Nil => match ys {
                NList::Nil => (),
                NList::Cons(_h2, _t2) => (),
            },
            NList::Cons(_h, t) => match ys.clone() {
                // app(xs, Nil) == xs, so both sides are last(xs).
                NList::Nil => app_nil(*t),
                // last(Cons(h, app(t, ys))) needs the shape of app(t, ys).
                NList::Cons(_h2, _t2) => match *t.clone() {
                    NList::Nil => (),
                    NList::Cons(_h3, t3) => {
                        // Inner term: app(t, ys) unfolds to Cons(h3, app(t3, ys)).
                        instantiate!(app(t3, ys));
                        tip_61(*t, ys);
                    }
                },
            },
        }
    }
}
