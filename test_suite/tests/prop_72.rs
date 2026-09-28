// TIP IsaPlanner prop_72: rev(drop(i, xs)) == take(sub(len(xs), i), rev(xs))
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
    fn drop(n: Nat, xs: List) -> List {
        match n {
            Nat::Z => xs,
            Nat::S(n_min) => match xs {
                List::Nil => List::Nil,
                List::Cons(_h, t) => drop(*n_min, *t),
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
    fn sub(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => Nat::Z,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => sub(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn app(x: List, y: List) -> List {
        match x {
            List::Nil => y,
            List::Cons(h, t) => List::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val]
    #[recursive]
    fn rev(xs: List) -> List {
        match xs {
            List::Nil => List::Nil,
            List::Cons(h, t) => app(rev(*t), List::Cons(h, Box::new(List::Nil))),
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

    // Helper: Z is a right identity of sub.
    #[val((n: Nat) -> Lemma(sub(n, Nat::Z) == n))]
    fn sub_zero(n: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(_n_min) => (),
        }
    }

    // Helper: le is reflexive.
    #[val((n: Nat) -> Lemma(le(n, n)))]
    fn le_refl(n: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => le_refl(*n_min),
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

    // Helper: subtraction never exceeds its first argument.
    #[val((n: Nat, m: Nat) -> Lemma(le(sub(n, m), n)))]
    fn sub_le(n: Nat, m: Nat) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => match m {
                Nat::Z => le_refl(*n_min),
                Nat::S(m_min) => {
                    sub_le(*n_min.clone(), *m_min.clone());
                    le_succ(sub(*n_min.clone(), *m_min), *n_min);
                }
            },
        }
    }

    // Helper: appending one element adds one to the length.
    #[val((xs: List, x: Elem) -> Lemma(len(app(xs, List::Cons(x, Box::new(List::Nil)))) == Nat::S(len(xs))))]
    fn len_app_one(xs: List, x: Elem) {
        match xs {
            List::Nil => (),
            List::Cons(_h, t) => len_app_one(*t, x),
        }
    }

    // Helper: rev preserves length.
    #[val((xs: List) -> Lemma(len(rev(xs)) == len(xs)))]
    fn len_rev(xs: List) {
        match xs {
            List::Nil => (),
            List::Cons(h, t) => {
                len_app_one(rev(*t.clone()), h);
                len_rev(*t);
            }
        }
    }

    // Helper: taking a list's whole length gives the list back.
    #[val((xs: List) -> Lemma(take(len(xs), xs) == xs))]
    fn take_len(xs: List) {
        match xs {
            List::Nil => (),
            List::Cons(_h, t) => take_len(*t),
        }
    }

    // Helper: a take within the first list ignores what is appended after it.
    #[val((k: Nat, ys: List, zs: List) -> Lemma(implies(le(k, len(ys)), take(k, app(ys, zs)) == take(k, ys))))]
    fn take_app_le(k: Nat, ys: List, zs: List) {
        match k {
            Nat::Z => (),
            Nat::S(k_min) => match ys {
                List::Nil => (),
                List::Cons(_h, t) => take_app_le(*k_min, *t, zs),
            },
        }
    }

    // Induction on i with a case split on xs. The i == Z case is
    // take(len(xs), rev(xs)) == rev(xs) after sub_zero, via len_rev and
    // take_len. In the S/Cons case the right side is a take of
    // sub(len(t), i') from app(rev(t), [h]); that count is at most len(t)
    // (sub_le) == len(rev(t)) (len_rev), so take_app_le drops the appended
    // element and the induction hypothesis closes the goal.
    #[val((i: Nat, xs: List) -> Lemma(rev(drop(i, xs)) == take(sub(len(xs), i), rev(xs))))]
    fn tip_72(i: Nat, xs: List) {
        match i {
            Nat::Z => {
                sub_zero(len(xs.clone()));
                len_rev(xs.clone());
                take_len(rev(xs));
            }
            Nat::S(i_min) => match xs {
                List::Nil => (),
                List::Cons(h, t) => {
                    sub_le(len(*t.clone()), *i_min.clone());
                    len_rev(*t.clone());
                    take_app_le(
                        sub(len(*t.clone()), *i_min.clone()),
                        rev(*t.clone()),
                        List::Cons(h, Box::new(List::Nil)),
                    );
                    tip_72(*i_min, *t);
                }
            },
        }
    }
}
