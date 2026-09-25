// TIP IsaPlanner prop_03: le(count(n, xs), count(n, app(xs, ys)))
//
// Induction on xs. The Nil case is le(Z, _), true by le's first equation.
// In the Cons step both counts unfold through the same guard eq_nat(n, h)
// and le's S/S equation reduces the goal to the induction hypothesis.
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
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((n: Nat, xs: NList, ys: NList) -> Lemma(le(count(n, xs), count(n, app(xs, ys)))))]
    fn tip_03(n: Nat, xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // count's guard at the head, shared by both sides.
                instantiate!(eq_nat(n, h));
                tip_03(n, *t, ys);
            }
        }
    }
}
