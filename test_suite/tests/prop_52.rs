// TIP IsaPlanner prop_52: count(n, rev(xs)) == count(n, xs)
//
// A genuine multi-helper proof: the main lemma leans on THREE helpers,
//   count_app (TIP prop_02):  count over an append splits into an add
//   add_zero:                 add(x, Z) == x
//   add_one:                  add(x, S(Z)) == S(x)
// The Cons step rewrites rev(Cons(h, t)) to app(rev(t), [h]), splits the
// count with count_app, evaluates count(n, [h]) to S(Z) or Z depending on
// the eq_nat(n, h) guard, and folds the add back with add_one/add_zero.
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

    #[val]
    #[recursive]
    fn rev(x: NList) -> NList {
        match x {
            NList::Nil => NList::Nil,
            NList::Cons(h, t) => app(rev(*t), NList::Cons(h, Box::new(NList::Nil))),
        }
    }

    // Helper: add(x, Z) == x.
    #[val((x: Nat) -> Lemma(add(x, Nat::Z) == x))]
    fn add_zero(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                add_zero(*x_min);
            }
        }
    }

    // Helper: add(x, S(Z)) == S(x).
    #[val((x: Nat) -> Lemma(add(x, Nat::S(Nat::Z)) == Nat::S(x)))]
    fn add_one(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                add_one(*x_min);
            }
        }
    }

    // Helper (TIP prop_02): count distributes over append.
    #[val((n: Nat, xs: NList, ys: NList) ->
        Lemma(count(n, app(xs, ys)) == add(count(n, xs), count(n, ys))))]
    fn count_app(n: Nat, xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The unfolding of app, the guard of count's Cons equations,
                // and the S-wrapped values both sides of the goal pass through
                // when the eq_nat(n, h) guard holds.
                instantiate!(eq_nat(n, h));
                count_app(n, *t, ys);
            }
        }
    }

    #[val((n: Nat, xs: NList) -> Lemma(count(n, rev(xs)) == count(n, xs)))]
    fn tip_52(n: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // rev(Cons(h, t)) = app(rev(t), [h]); count(n, [h]) evaluates
                // through count's guard to S(Z) or Z.
                instantiate!(eq_nat(n, h));
                count_app(
                    n.clone(),
                    rev(*t.clone()),
                    NList::Cons(h.clone(), Box::new(NList::Nil)),
                );
                add_one(count(n.clone(), *t.clone()));
                add_zero(count(n.clone(), *t.clone()));
                tip_52(n, *t);
            }
        }
    }
}
