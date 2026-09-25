// TIP IsaPlanner prop_75: add(count(n, xs), count(n, Cons(m, Nil))) == count(n, Cons(m, xs))
//
// No induction, but unlike prop_39 the S from the singleton sits on the
// RIGHT of add, so the goal is add(c, S(Z)) == S(c) or add(c, Z) == c for
// c = count(n, xs): the add_zero and add_one helpers, selected by the
// guard eq_nat(n, m).
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
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
        }
    }

    // Helper: add(x, Z) == x.
    #[val((x: Nat) -> Lemma(add(x, Nat::Z) == x))]
    fn add_zero(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => add_zero(*x_min),
        }
    }

    // Helper: add(x, S(Z)) == S(x).
    #[val((x: Nat) -> Lemma(add(x, Nat::S(Nat::Z)) == Nat::S(x)))]
    fn add_one(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => add_one(*x_min),
        }
    }

    #[val((n: Nat, m: Nat, xs: NList) ->
        Lemma(add(count(n, xs), count(n, NList::Cons(m, Box::new(NList::Nil)))) == count(n, NList::Cons(m, xs))))]
    fn tip_75(n: Nat, m: Nat, xs: NList) {
        instantiate!(eq_nat(n, m));
        add_zero(count(n.clone(), xs.clone()));
        add_one(count(n, xs));
    }
}
