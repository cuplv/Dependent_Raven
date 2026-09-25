// TIP IsaPlanner prop_59: implies(ys == Nil, last(app(xs, ys)) == last(xs))
//
// The simplest lemma-requiring benchmark: under the hypothesis the goal is
// last(app(xs, Nil)) == last(xs), and app cannot unfold at the variable xs.
// The helper app_nil (Nil is a right identity of app) closes it outright;
// the main proof needs no induction of its own.
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

    // Helper: Nil is a right identity of app.
    #[val((xs: NList) -> Lemma(app(xs, NList::Nil) == xs))]
    fn app_nil(xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(_h, t) => app_nil(*t),
        }
    }

    // No induction: with ys == Nil the goal is last(app(xs, Nil)) == last(xs),
    // which app_nil closes outright.
    #[val((xs: NList, ys: NList) -> Lemma(implies(ys == NList::Nil, last(app(xs, ys)) == last(xs))))]
    fn tip_59(xs: NList, _ys: NList) {
        app_nil(xs);
    }
}
