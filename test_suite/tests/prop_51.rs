// TIP IsaPlanner prop_51: butlast(app(xs, Cons(x, Nil))) == xs
//
// Induction on xs. In the Cons step butlast(Cons(h, app(t, [x]))) unfolds
// only once app(t, [x]) has a known shape, so the step splits on t: for
// t == Nil it is butlast(Cons(h, Cons(x, Nil))) == Cons(h, Nil); otherwise
// app(t, [x]) is a Cons and the induction hypothesis at t closes the goal.
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

    #[val((xs: List, x: Elem) -> Lemma(butlast(app(xs, List::Cons(x, Box::new(List::Nil)))) == xs))]
    fn tip_51(xs: List, x: Elem) {
        match xs {
            List::Nil => (),
            List::Cons(_h, t) => match *t.clone() {
                List::Nil => (),
                List::Cons(_h2, t2) => {
                    // Inner term: app(t, [x]) unfolds to Cons(h2, app(t2, [x])).
                    instantiate!(app(t2, List::Cons(x, List::Nil)));
                    tip_51(*t, x);
                }
            },
        }
    }
}
