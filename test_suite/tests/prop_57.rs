// TIP IsaPlanner prop_57: drop(n, take(m, xs)) == take(sub(m, n), drop(n, xs))
//
// Induction on n with case splits on m and xs. Two helpers of different
// kinds: sub_zero (the n == Z case is take(sub(m, Z), xs) == take(m, xs))
// and take_nil (the S/S/Nil case is take(sub(m', n'), Nil) == Nil with a
// variable count). The S/S/Cons case is the induction hypothesis.
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

    // Helper: take of Nil is Nil, whatever the count.
    #[val((k: Nat) -> Lemma(take(k, List::Nil) == List::Nil))]
    fn take_nil(k: Nat) {
        match k {
            Nat::Z => (),
            Nat::S(_k_min) => (),
        }
    }

    #[val((n: Nat, m: Nat, xs: List) -> Lemma(drop(n, take(m, xs)) == take(sub(m, n), drop(n, xs))))]
    fn tip_57(n: Nat, m: Nat, xs: List) {
        match n {
            // take(sub(m, Z), xs) == take(m, xs).
            Nat::Z => sub_zero(m),
            Nat::S(n_min) => match m {
                Nat::Z => (),
                Nat::S(m_min) => match xs {
                    // take(sub(m', n'), Nil) with a variable count.
                    List::Nil => take_nil(sub(*m_min, *n_min)),
                    List::Cons(_h, t) => {
                        tip_57(*n_min, *m_min, *t);
                    }
                },
            },
        }
    }
}
