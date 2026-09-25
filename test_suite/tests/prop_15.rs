// TIP IsaPlanner prop_15: len(ins(x, xs)) == S(len(xs))
//
// Induction on xs. The Cons step splits on the guard lt(x, h): if it
// holds, ins returns Cons(x, Cons(h, t)) and both sides are S(S(len(t)));
// otherwise ins returns Cons(h, ins(x, t)) and the induction hypothesis
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
    fn len(xs: NList) -> Nat {
        match xs {
            NList::Nil => Nat::Z,
            NList::Cons(_h, t) => Nat::S(Box::new(len(*t))),
        }
    }

    // TIP's `<2`: matches the second argument first.
    #[val]
    #[recursive]
    fn lt(x: Nat, y: Nat) -> bool {
        match y {
            Nat::Z => false,
            Nat::S(y_min) => match x {
                Nat::Z => true,
                Nat::S(x_min) => lt(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn ins(x: Nat, xs: NList) -> NList {
        match xs {
            NList::Nil => NList::Cons(x, Box::new(NList::Nil)),
            NList::Cons(h, t) => {
                if lt(x.clone(), h.clone()) {
                    NList::Cons(x, Box::new(NList::Cons(h, t)))
                } else {
                    NList::Cons(h, Box::new(ins(x, *t)))
                }
            }
        }
    }

    #[val((x: Nat, xs: NList) -> Lemma(len(ins(x, xs)) == Nat::S(len(xs))))]
    fn tip_15(x: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guard of ins's Cons equation.
                instantiate!(lt(x, h));
                tip_15(x, *t);
            }
        }
    }
}
