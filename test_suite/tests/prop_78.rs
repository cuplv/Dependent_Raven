// TIP IsaPlanner prop_78: sorted(sort(xs))
//
// The sorting-cluster flagship, and the canonical two-level lemma chain:
// tip_78 leans on sorted_insort (insertion preserves sortedness -- the
// prop_77 lemma), whose own proof leans on le_neg (totality of le). The
// top proof itself is tiny: one helper call at (h, sort(t)) plus the
// induction hypothesis; sort's defining equation and functionality do
// the rest.
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

    // Helper (depth 1): insertion preserves sortedness (TIP prop_77).
    #[val((x: Nat, xs: NList) -> Lemma(implies(sorted(xs), sorted(insort(x, xs)))))]
    fn sorted_insort(x: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                le_neg(x.clone(), h.clone());
                instantiate!(NList::Cons(h, insort(x, t)));
                match *t.clone() {
                    NList::Nil => (),
                    NList::Cons(h2, t2) => {
                        instantiate!(le(h, h2));
                        instantiate!(le(x, h2));
                        instantiate!(sorted(NList::Cons(h2, insort(x, t2))));
                        sorted_insort(x.clone(), *t.clone());
                    }
                }
            }
        }
    }

    #[val((xs: NList) -> Lemma(sorted(sort(xs))))]
    fn tip_78(xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                sorted_insort(h.clone(), sort(*t.clone()));
                tip_78(*t)
            }
        }
    }
}
