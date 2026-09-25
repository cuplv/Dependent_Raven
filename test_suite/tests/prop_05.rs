// TIP IsaPlanner prop_05: implies(n == x, S(count(n, xs)) == count(n, Cons(x, xs)))
//
// One unfolding of count through the guard eq_nat(n, x), which under the
// hypothesis is eq_nat(n, n) and must hold: the eq_refl helper.
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

    // Helper: eq_nat is reflexive.
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }

    #[val((n: Nat, x: Nat, xs: NList) -> Lemma(implies(n == x, Nat::S(count(n, xs)) == count(n, NList::Cons(x, xs)))))]
    fn tip_05(n: Nat, _x: Nat, _xs: NList) {
        eq_refl(n);
    }
}
