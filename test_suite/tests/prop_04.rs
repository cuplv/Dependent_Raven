// G3 test 2 / TIP IsaPlanner prop_04: S(count(n, xs)) == count(n, Cons(n, xs))
// `count` has an `if` in its body -- the definitional-axiom generator must
// flatten it into guarded equations (G3 step 3). Proof needs no induction:
// eq_refl(n) supplies the guard of the then-branch equation.
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

    // Helper: eq_nat is reflexive (discharges the then-branch guard).
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }

    #[val((n: Nat, xs: NList) -> Lemma(Nat::S(Box::new(count(n, xs))) == count(n, NList::Cons(n, Box::new(xs)))))]
    #[allow(unused_variables)]
    fn tip_04(n: Nat, xs: NList) {
        eq_refl(n)
    }
}
