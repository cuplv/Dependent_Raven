// TIP IsaPlanner prop_77: sorted(xs) ==> sorted(insort(x, xs))
//
// The first property with an IMPLICATION goal, written with the parser's
// implies(p, q) form. The proof mixes every ingredient: a conditional
// helper lemma (le_neg: from !le(x, y) conclude le(y, x)), guard case
// splits in the proof body (if le(..)), a nested match to expose the head
// of the tail (sorted's equations need the first TWO elements), and
// instantiations naming the lists insort builds.
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

    // Helper: le is total -- if x is not below y, then y is below x.
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

    // The guard case split on le(x, h) is left to the solver: le_neg's gated
    // postcondition (le(h, x)) engages exactly when the guard is false. The
    // guard-true outcome Cons(x, Cons(h, t)) is pinned by insort's equation;
    // the guard-false outcome Cons(h, insort(x, t)) contains the inner term
    // insort(x, t) and has to be named. Below the head, sorted's equations
    // need the guards le(h, h2), le(x, h2) and the list insort builds there.
    #[val((x: Nat, xs: NList) -> Lemma(implies(sorted(xs), sorted(insort(x, xs)))))]
    fn tip_77(x: Nat, xs: NList) {
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
                        tip_77(x.clone(), *t.clone());
                    }
                }
            }
        }
    }
}
