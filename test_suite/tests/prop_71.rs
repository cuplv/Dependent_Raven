// TIP IsaPlanner prop_71: implies(!eq_nat(x, y), elem(x, ins(y, xs)) == elem(x, xs))
//
// Induction on xs, no helper: the hypothesis is itself the guard elem meets
// wherever ins puts y, so unlike prop_86 nothing has to be derived. The
// remaining guards, lt(y, h) and eq_nat(x, h), only need to exist; both
// outcomes close, the last by the induction hypothesis.
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
    fn eq_nat(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => match y {
                Nat::Z => true,
                Nat::S(_y_min) => false,
            },
            Nat::S(x_min) => match y {
                Nat::Z => false,
                Nat::S(y_min) => eq_nat(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn elem(x: Nat, xs: NList) -> bool {
        match xs {
            NList::Nil => false,
            NList::Cons(h, t) => {
                if eq_nat(x.clone(), h) {
                    true
                } else {
                    elem(x, *t)
                }
            }
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

    #[val((x: Nat, y: Nat, xs: NList) -> Lemma(implies(!eq_nat(x, y), elem(x, ins(y, xs)) == elem(x, xs))))]
    fn tip_71(x: Nat, y: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guards of ins's and elem's Cons equations; the
                // hypothesis !eq_nat(x, y) settles the guard at y itself.
                instantiate!(lt(y, h));
                instantiate!(eq_nat(x, h));
                tip_71(x, y, *t);
            }
        }
    }
}
