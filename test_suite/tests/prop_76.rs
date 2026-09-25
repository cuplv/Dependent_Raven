// TIP IsaPlanner prop_76:
//   implies(!eq_nat(n, m), count(n, app(xs, Cons(m, Nil))) == count(n, xs))
//
// Induction on xs. In the Nil case count(n, Cons(m, Nil)) unfolds through
// the guard eq_nat(n, m), which the hypothesis says is false, to
// count(n, Nil) == Z. The Cons step unfolds both sides through
// eq_nat(n, h) and closes by the induction hypothesis at t.
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
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((n: Nat, m: Nat, xs: NList) ->
        Lemma(implies(!eq_nat(n, m),
                      count(n, app(xs, NList::Cons(m, Box::new(NList::Nil)))) == count(n, xs))))]
    fn tip_76(n: Nat, m: Nat, xs: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(h, t) => {
                // The guard of count's Cons equation at the head.
                instantiate!(eq_nat(n, h));
                tip_76(n, m, *t);
            }
        }
    }
}
