// Logical connectives in PROGRAM position (function bodies): `!`, `&&`, `||`
// inside `if` conditions and as a Bool-returning tail. Previously any of these
// panicked in the checker ("T-LOGIC not implemented"); in spec position they
// always worked. T-LOGIC synthesizes the operands and returns the selfified
// Bool `{v: Bool | v == (a op b)}`.
#[ravencheck::module]
mod bool_connectives {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[val]
    fn is_zero(n: Nat) -> bool {
        match n {
            Nat::Z => true,
            Nat::S(_) => false,
        }
    }

    // `!` in a condition.
    #[val]
    fn nonzero_or_z(n: Nat) -> Nat {
        if !is_zero(n.clone()) { n } else { Nat::Z }
    }

    // `&&` in a condition.
    #[val]
    fn both_zero_gate(a: Nat, b: Nat) -> Nat {
        if is_zero(a) && is_zero(b) { Nat::Z } else { Nat::S(Box::new(Nat::Z)) }
    }

    // `||` as a Bool-returning tail.
    #[val]
    fn either_zero(a: Nat, b: Nat) -> bool {
        is_zero(a) || is_zero(b)
    }

    #[val((m: Nat) -> Lemma(nonzero_or_z(Nat::S(Box::new(m))) == Nat::S(Box::new(m))))]
    fn nonzero_or_z_s(m: Nat) {
        instantiate!(is_zero(Nat::S(m)));
    }

    #[val((m: Nat) -> Lemma(both_zero_gate(Nat::Z, Nat::Z) == Nat::Z))]
    fn both_zero_gate_zz(m: Nat) {
        instantiate!(is_zero(Nat::Z));
    }

    #[val((n: Nat) -> Lemma(both_zero_gate(Nat::S(Box::new(n)), Nat::Z) == Nat::S(Box::new(Nat::Z))))]
    fn both_zero_gate_sz(n: Nat) {
        instantiate!(is_zero(Nat::S(n)));
    }

    #[val((n: Nat) -> Lemma(either_zero(Nat::S(Box::new(n)), Nat::Z)))]
    fn either_zero_sz(n: Nat) {
        instantiate!(is_zero(Nat::S(n)));
        instantiate!(is_zero(Nat::Z));
    }
}
