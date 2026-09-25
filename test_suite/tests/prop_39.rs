// TIP IsaPlanner prop_39: add(count(n, Cons(x, Nil)), count(n, xs)) == count(n, Cons(x, xs))
//
// No induction: both count(n, Cons(x, ·)) terms unfold through the same
// guard eq_nat(n, x), which only has to exist; add then unfolds once or
// twice on the literal S(Z) / Z.
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

    #[val((n: Nat, x: Nat, xs: NList) ->
        Lemma(add(count(n, NList::Cons(x, Box::new(NList::Nil))), count(n, xs)) == count(n, NList::Cons(x, xs))))]
    fn tip_39(n: Nat, x: Nat, _xs: NList) {
        instantiate!(eq_nat(n, x));
    }
}
