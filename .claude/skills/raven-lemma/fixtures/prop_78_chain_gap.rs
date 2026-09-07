// TIP IsaPlanner prop_78: sorted(sort(xs))
//
// Lemma-gap fixture: the induction hypothesis is present, one proven
// helper (le_neg) exists in the module, and the instantiate procedure
// has run to saturation (the hint in the Cons branch is its work). The
// verification still fails.
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
    fn le(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(x_min) => match y {
                Nat::Z => false,
                Nat::S(y_min) => le(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn insort(x: Nat, xs: NList) -> NList {
        match xs {
            NList::Nil => NList::Cons(x, Box::new(NList::Nil)),
            NList::Cons(h, t) => {
                if le(x.clone(), h.clone()) {
                    NList::Cons(x, Box::new(NList::Cons(h, t)))
                } else {
                    NList::Cons(h, Box::new(insort(x, *t)))
                }
            }
        }
    }

    #[val]
    #[recursive]
    fn sort(xs: NList) -> NList {
        match xs {
            NList::Nil => NList::Nil,
            NList::Cons(h, t) => insort(h, sort(*t)),
        }
    }

    #[val]
    #[recursive]
    fn sorted(xs: NList) -> bool {
        match xs {
            NList::Nil => true,
            NList::Cons(h, t) => match *t {
                NList::Nil => true,
                NList::Cons(h2, t2) => {
                    if le(h, h2.clone()) {
                        sorted(NList::Cons(h2, t2))
                    } else {
                        false
                    }
                }
            },
        }
    }

    // Helper (depth 2): le is total -- if x is not below y, y is below x.
    #[val((x: Nat, y: Nat) -> Lemma(implies(!le(x, y), le(y, x))))]
    fn le_neg(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => le_neg(*x_min, *y_min),
            },
        }
    }

    #[val((xs: NList) -> Lemma(sorted(sort(xs))))]
    fn tip_78(xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                instantiate!(insort(h, sort(t)));
                tip_78(*t)
            }
        }
    }
}
