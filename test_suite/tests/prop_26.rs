// TIP IsaPlanner prop_26: implies(elem(x, xs), elem(x, app(xs, ys)))
//
// Induction on xs. In the Cons step both elem applications unfold through
// the same guard eq_nat(x, h): if it holds both are true; otherwise the
// hypothesis becomes elem(x, t) and the induction hypothesis at t gives
// elem(x, app(t, ys)).
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

    #[val]
    #[recursive]
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((x: Nat, xs: NList, ys: NList) -> Lemma(implies(elem(x, xs), elem(x, app(xs, ys)))))]
    fn tip_26(x: Nat, xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guard both elem applications unfold through.
                instantiate!(eq_nat(x, h));
                tip_26(x, *t, ys);
            }
        }
    }
}
