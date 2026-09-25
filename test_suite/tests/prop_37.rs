// TIP IsaPlanner prop_37: !elem(x, delete(x, xs))
//
// Induction on xs. The Cons step splits on the guard eq_nat(x, h): if it
// holds, delete drops h and the goal is the induction hypothesis at t;
// otherwise delete keeps h, elem unfolds through the same (false) guard
// and again reduces to the induction hypothesis.
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
    fn delete(x: Nat, xs: NList) -> NList {
        match xs {
            NList::Nil => NList::Nil,
            NList::Cons(h, t) => {
                if eq_nat(x.clone(), h.clone()) {
                    delete(x, *t)
                } else {
                    NList::Cons(h, Box::new(delete(x, *t)))
                }
            }
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

    #[val((x: Nat, xs: NList) -> Lemma(!elem(x, delete(x, xs))))]
    fn tip_37(x: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guard shared by delete's and elem's Cons equations.
                instantiate!(eq_nat(x, h));
                tip_37(x, *t);
            }
        }
    }
}
