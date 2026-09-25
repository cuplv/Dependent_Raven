// TIP IsaPlanner prop_68: le(len(delete(n, xs)), len(xs))
//
// Induction on xs. The Cons step splits on the guard eq_nat(n, h): if it
// holds, delete drops h and the goal weakens the induction hypothesis by
// one on the right (helper le_succ); otherwise both lengths grow by one
// and le unfolds straight to the induction hypothesis.
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
    fn le(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(x_min) => match y {
                Nat::Z => false,
                Nat::S(y_min) => le(*x_min, *y_min),
            },
        }
    }

    // Helper: le is preserved by a successor on the right.
    #[val((a: Nat, b: Nat) -> Lemma(implies(le(a, b), le(a, Nat::S(b)))))]
    fn le_succ(a: Nat, b: Nat) {
        match a {
            Nat::Z => (),
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => le_succ(*a_min, *b_min),
            },
        }
    }

    #[val((n: Nat, xs: NList) -> Lemma(le(len(delete(n, xs)), len(xs))))]
    fn tip_68(n: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guard of delete's Cons equation.
                instantiate!(eq_nat(n, h));
                le_succ(len(delete(n.clone(), *t.clone())), len(*t.clone()));
                tip_68(n, *t);
            }
        }
    }
}
