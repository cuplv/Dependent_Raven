// Demo: add(S(S(Z)), x) == S(S(x)) with no induction and no hints.
#[ravencheck::module]
mod demo {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[val]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
        }
    }

    #[val((x: Nat) -> Lemma(add(Nat::S(Nat::S(Nat::Z)), x) == Nat::S(Nat::S(x))))]
    fn two_plus(x: Nat) {
        instantiate!(add(Nat::S(Nat::Z), x));
    }
}
