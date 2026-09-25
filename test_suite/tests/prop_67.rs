// TIP IsaPlanner prop_67: len(butlast(xs)) == sub(len(xs), S(Z))
//
// Induction on xs with a case split on t (butlast needs the first two
// elements). In the Cons/Cons step both sides reduce to S(sub(len(t2), Z))
// versus S(len(t2)), and sub cannot unfold at the variable len(t2): the
// helper sub_zero (Z is a right identity of sub) supplies that equation.
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

    #[val((xs: List) -> Lemma(len(butlast(xs)) == sub(len(xs), Nat::S(Nat::Z))))]
    fn tip_67(xs: List) {
        match xs {
            List::Nil => (),
            List::Cons(_h, t) => match *t.clone() {
                List::Nil => (),
                List::Cons(_h2, t2) => {
                    // The step reduces to S(sub(len(t2), Z)) == S(len(t2)).
                    sub_zero(len(*t2));
                    tip_67(*t);
                }
            },
        }
    }
}
