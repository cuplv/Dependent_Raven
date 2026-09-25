// TIP IsaPlanner prop_30: elem(x, ins(x, xs))
//
// Induction on xs. Wherever ins puts x, elem meets the guard eq_nat(x, x),
// which must hold (helper eq_refl). The other guards, lt(x, h) for ins and
// eq_nat(x, h) for elem, only have to exist; the last outcome is the
// induction hypothesis.
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

    // Helper: eq_nat is reflexive.
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }

    #[val((x: Nat, xs: NList) -> Lemma(elem(x, ins(x, xs))))]
    fn tip_30(x: Nat, xs: NList) {
        eq_refl(x.clone());
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                instantiate!(lt(x, h));
                instantiate!(eq_nat(x, h));
                tip_30(x, *t);
            }
        }
    }
}
