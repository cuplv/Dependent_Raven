// TIP IsaPlanner prop_53: count(n, xs) == count(n, sort(xs))
//
// Two-level chain: the main lemma leans on count_insort (inserting x
// anywhere counts the same as putting it in front), applied at
// (n, h, sort(t)); with count's guard eq_nat(n, h) named, both
// count(n, Cons(h, t)) and count(n, Cons(h, sort(t))) unfold alike and the
// induction hypothesis closes the goal. The helper's own step needs three
// guards (le(x, h), eq_nat(n, h), eq_nat(n, x)) and two inner terms
// (count(n, s), count(n, t)) before its induction hypothesis applies.
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
    fn count(x: Nat, xs: NList) -> Nat {
        match xs {
            NList::Nil => Nat::Z,
            NList::Cons(h, t) => {
                if eq_nat(x.clone(), h) {
                    Nat::S(Box::new(count(x, *t)))
                } else {
                    count(x, *t)
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

    // Helper: inserting x anywhere counts the same as putting it in front.
    #[val((n: Nat, x: Nat, s: NList) -> Lemma(count(n, insort(x, s)) == count(n, NList::Cons(x, s))))]
    fn count_insort(n: Nat, x: Nat, s: NList) {
        match s {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // insort's guard, and count's guard at both heads.
                instantiate!(le(x, h));
                instantiate!(eq_nat(n, h));
                instantiate!(eq_nat(n, x));
                // Inner terms: count(n, Cons(x, s)) unfolds to S?(count(n, s)),
                // and count(n, s) as well as count(n, Cons(x, t)) to
                // S?(count(n, t)).
                instantiate!(count(n, s));
                instantiate!(count(n, t));
                count_insort(n, x, *t);
            }
        }
    }

    #[val((n: Nat, xs: NList) -> Lemma(count(n, xs) == count(n, sort(xs))))]
    fn tip_53(n: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // count's guard at h, shared by count(n, Cons(h, t)) and
                // count(n, Cons(h, sort(t))).
                instantiate!(eq_nat(n, h));
                count_insort(n.clone(), h.clone(), sort(*t.clone()));
                tip_53(n, *t);
            }
        }
    }
}
