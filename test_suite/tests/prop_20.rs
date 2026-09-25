// TIP IsaPlanner prop_20: len(sort(xs)) == len(xs)
//
// Two-level chain, like prop_78: the main lemma leans on len_insort
// (insertion adds exactly one element -- prop_15 with le in place of
// lt), applied at (h, sort(t)); the induction hypothesis at t does the
// rest.
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

    // Helper: insertion adds exactly one element (prop_15 for insort).
    #[val((x: Nat, xs: NList) -> Lemma(len(insort(x, xs)) == Nat::S(len(xs))))]
    fn len_insort(x: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guard of insort's Cons equation.
                instantiate!(le(x, h));
                len_insort(x, *t);
            }
        }
    }

    #[val((xs: NList) -> Lemma(len(sort(xs)) == len(xs)))]
    fn tip_20(xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                len_insort(h, sort(*t.clone()));
                tip_20(*t);
            }
        }
    }
}
