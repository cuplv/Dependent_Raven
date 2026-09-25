// TIP IsaPlanner prop_50: butlast(xs) == take(sub(len(xs), S(Z)), xs)
//
// Induction on xs with a case split on t. In the Cons/Cons step the right
// side is take(sub(S(len(t)), S(Z)), xs) == take(sub(len(t), Z), xs), and
// take cannot unfold until sub(len(t), Z) is known to be len(t) = S(len(t2));
// the induction hypothesis carries the same sub(len(t2), Z) one level down.
// The helper sub_zero (Z is a right identity of sub) supplies both.
#[ravencheck::module]
mod tip_benchmarks {

    // Uninterpreted element sort (the benchmark is polymorphic in `a`).
    #[declare]
    type Elem = u32;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum List {
        Nil,
        Cons(Elem, Box<List>),
    }

    #[val]
    #[recursive]
    fn take(n: Nat, xs: List) -> List {
        match n {
            Nat::Z => List::Nil,
            Nat::S(n_min) => match xs {
                List::Nil => List::Nil,
                List::Cons(h, t) => List::Cons(h, Box::new(take(*n_min, *t))),
            },
        }
    }

    #[val]
    #[recursive]
    fn len(xs: List) -> Nat {
        match xs {
            List::Nil => Nat::Z,
            List::Cons(_h, t) => Nat::S(Box::new(len(*t))),
        }
    }

    #[val]
    #[recursive]
    fn butlast(xs: List) -> List {
        match xs {
            List::Nil => List::Nil,
            List::Cons(h, t) => match *t {
                List::Nil => List::Nil,
                List::Cons(h2, t2) => List::Cons(h, Box::new(butlast(List::Cons(h2, t2)))),
            },
        }
    }

    #[val]
    #[recursive]
    fn sub(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => Nat::Z,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => sub(*x_min, *y_min),
            },
        }
    }

    // Helper: Z is a right identity of sub.
    #[val((n: Nat) -> Lemma(sub(n, Nat::Z) == n))]
    fn sub_zero(n: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(_n_min) => (),
        }
    }

    #[val((xs: List) -> Lemma(butlast(xs) == take(sub(len(xs), Nat::S(Nat::Z)), xs)))]
    fn tip_50(xs: List) {
        match xs {
            List::Nil => (),
            List::Cons(_h, t) => match *t.clone() {
                List::Nil => (),
                List::Cons(_h2, t2) => {
                    // sub(S(len(t)), S(Z)) == sub(len(t), Z) == len(t) on the
                    // right; the induction hypothesis carries the same
                    // shape one level down at len(t2).
                    sub_zero(len(*t.clone()));
                    sub_zero(len(*t2));
                    tip_50(*t);
                }
            },
        }
    }
}
