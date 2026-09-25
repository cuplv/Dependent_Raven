// TIP IsaPlanner prop_49: butlast(app(xs, ys)) == butlast_concat(xs, ys)
//
// Induction on xs with a case split on ys (butlast_concat matches on ys).
// The ys == Nil branch is the app_nil helper; the ys == Cons branch needs
// the shape of app(t, ys) -- a case split on t -- and the inner terms of
// butlast_concat's Cons equation app(xs, butlast(ys)), which unfold through
// butlast(ys) and app(t, butlast(ys)).
#[ravencheck::module]
mod tip_benchmarks {

    // Uninterpreted element sort (the benchmark is polymorphic in `a`).
    #[declare]
    type Elem = u32;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum List {
        Nil,
        Cons(Elem, Box<List>),
    }

    #[val]
    #[recursive]
    fn butlast(xs: List) -> List {
        match xs {
            List::Nil => List::Nil,
            List::Cons(h, t) => match *t {
                List::Nil => List::Nil,
                List::Cons(h2, t2) => List::Cons(h, Box::new(butlast(List::Cons(h2, t2)))),
            },
        }
    }

    #[val]
    #[recursive]
    fn app(x: List, y: List) -> List {
        match x {
            List::Nil => y,
            List::Cons(h, t) => List::Cons(h, Box::new(app(*t, y))),
        }
    }

    // TIP's butlastConcat (non-recursive).
    #[val]
    fn butlast_concat(xs: List, ys: List) -> List {
        match ys {
            List::Nil => butlast(xs),
            List::Cons(h, t) => app(xs, butlast(List::Cons(h, t))),
        }
    }

    // Helper: Nil is a right identity of app.
    #[val((xs: List) -> Lemma(app(xs, List::Nil) == xs))]
    fn app_nil(xs: List) {
        match xs {
            List::Nil => (),
            List::Cons(_h, t) => app_nil(*t),
        }
    }

    #[val((xs: List, ys: List) -> Lemma(butlast(app(xs, ys)) == butlast_concat(xs, ys)))]
    fn tip_49(xs: List, ys: List) {
        match xs {
            // butlast_concat matches on ys.
            List::Nil => match ys {
                List::Nil => (),
                List::Cons(_h2, _t2) => (),
            },
            List::Cons(_h, t) => match ys.clone() {
                // app(xs, Nil) == xs, so both sides are butlast(xs).
                List::Nil => app_nil(*t),
                // butlast(Cons(h, app(t, ys))) needs the shape of app(t, ys).
                List::Cons(_h2, _t2) => match *t.clone() {
                    // Inner terms of butlast_concat's Cons equation:
                    // app(xs, butlast(ys)) unfolds through butlast(ys) and
                    // app(t, butlast(ys)).
                    List::Nil => {
                        instantiate!(app(List::Nil, butlast(ys)));
                    }
                    List::Cons(_h3, t3) => {
                        // Inner term: app(t, ys) unfolds to Cons(h3, app(t3, ys)).
                        instantiate!(app(t3, ys));
                        instantiate!(app(t, butlast(ys)));
                        tip_49(*t, ys);
                    }
                },
            },
        }
    }
}
