// TIP IsaPlanner prop_86: implies(lt(x, y), elem(x, ins(y, xs)) == elem(x, xs))
//
// Induction on xs. A guard lemma from the hypothesis: wherever ins puts y,
// elem meets the guard eq_nat(x, y), and lt(x, y) must refute it (helper
// lt_neq). The remaining guards, lt(y, h) and eq_nat(x, h), only need to
// exist; both outcomes close, the last by the induction hypothesis.
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

    // Helper: strictly smaller numbers are not equal.
    #[val((x: Nat, y: Nat) -> Lemma(implies(lt(x, y), !eq_nat(x, y))))]
    fn lt_neq(x: Nat, y: Nat) {
        match y {
            Nat::Z => (),
            Nat::S(y_min) => match x {
                Nat::Z => (),
                Nat::S(x_min) => lt_neq(*x_min, *y_min),
            },
        }
    }

    #[val((x: Nat, y: Nat, xs: NList) -> Lemma(implies(lt(x, y), elem(x, ins(y, xs)) == elem(x, xs))))]
    fn tip_86(x: Nat, y: Nat, xs: NList) {
        match xs {
            // elem(x, Cons(y, Nil)) unfolds through eq_nat(x, y), which the
            // hypothesis lt(x, y) refutes.
            NList::Nil => lt_neq(x, y),
            NList::Cons(h, t) => {
                lt_neq(x.clone(), y.clone());
                // The guards of ins's and elem's Cons equations.
                instantiate!(lt(y, h));
                instantiate!(eq_nat(x, h));
                tip_86(x, y, *t);
            }
        }
    }
}
