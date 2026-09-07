// TIP IsaPlanner prop_04: S(count(n, xs)) == count(n, Cons(n, xs))
//
// Lemma-gap fixture: the instantiate procedure has already run to
// saturation on this proof (the guard switch in tip_04's body is its
// work) and the verification still fails. The missing piece is a FACT,
// not a term.
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

    #[val((n: Nat, xs: NList) -> Lemma(Nat::S(Box::new(count(n, xs))) == count(n, NList::Cons(n, Box::new(xs)))))]
    #[allow(unused_variables)]
    fn tip_04(n: Nat, xs: NList) {
        instantiate!(eq_nat(n, n));
    }
}
