// TIP IsaPlanner prop_63: implies(lt(n, len(xs)), last(drop(n, xs)) == last(xs))
//
// Induction on n with case splits on xs and, one level down, on t: last
// needs the first two elements, and for t == Nil the hypothesis
// lt(n', len(Nil)) is false. The S/Cons/Cons case is the induction
// hypothesis at (n', t). No helper, no hints.
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
    fn last(xs: NList) -> Nat {
        match xs {
            NList::Nil => Nat::Z,
            NList::Cons(h, t) => match *t {
                NList::Nil => h,
                NList::Cons(h2, t2) => last(NList::Cons(h2, t2)),
            },
        }
    }

    #[val]
    #[recursive]
    fn drop(n: Nat, xs: NList) -> NList {
        match n {
            Nat::Z => xs,
            Nat::S(n_min) => match xs {
                NList::Nil => NList::Nil,
                NList::Cons(_h, t) => drop(*n_min, *t),
            },
        }
    }

    // TIP's `<2`: matches the second argument first.
    #[val]
    #[recursive]
    fn lt(x: Nat, y: Nat) -> bool {
        match y {
            Nat::Z => false,
            Nat::S(y_min) => match x {
                Nat::Z => true,
                Nat::S(x_min) => lt(*x_min, *y_min),
            },
        }
    }

    #[val((n: Nat, xs: NList) -> Lemma(implies(lt(n, len(xs)), last(drop(n, xs)) == last(xs))))]
    fn tip_63(n: Nat, xs: NList) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => match xs {
                NList::Nil => (),
                // last(Cons(h, t)) needs the shape of t; for t == Nil the
                // hypothesis lt(n', Z) is false.
                NList::Cons(_h, t) => match *t.clone() {
                    NList::Nil => (),
                    NList::Cons(_h2, _t2) => {
                        tip_63(*n_min, *t);
                    }
                },
            },
        }
    }
}
