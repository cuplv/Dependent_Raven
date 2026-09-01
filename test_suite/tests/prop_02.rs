// TIP IsaPlanner prop_02: add(count(n, xs), count(n, ys)) == count(n, app(xs, ys))
//
// count distributes over append. Induction on xs; the Cons branch needs the
// guard of count's equations (eq_nat(n, h) -- without its switch both guarded
// equations are vacuous), the app unfolding, and the S-wrapped values that
// both sides pass through when the guard holds. The same proof serves as the
// count_app helper inside prop_52.
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
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
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
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((n: Nat, xs: NList, ys: NList) ->
        Lemma(add(count(n, xs), count(n, ys)) == count(n, app(xs, ys))))]
    fn tip_02(n: Nat, xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                instantiate!(eq_nat(n, h));
                instantiate!(NList::Cons(h, app(t, ys)));
                instantiate!(Nat::S(count(n, app(t, ys))));
                instantiate!(Nat::S(count(n, t)));
                instantiate!(Nat::S(add(count(n, t), count(n, ys))));
                tip_02(n, *t, ys)
            }
        }
    }
}
