// A bare `_` match arm. Arms are encoded as unordered cases, so at registration
// the `_` arm is replaced by the constructors the arms BEFORE it leave
// uncovered (Rust's first-match semantics), each carrying a copy of its body.
// The complement also descends below a constructor: after
// `VCons(Num(n), _)` the `_` arm covers `VCons(BoolV(_), _)`,
// `VCons(Unit0, _)` and `VNil`.
#[ravencheck::module]
mod match_catch_all {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Value {
        Num(Nat),
        BoolV(bool),
        Unit0,
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum VList {
        VNil,
        VCons(Value, Box<VList>),
    }

    #[val]
    fn is_num(v: Value) -> bool {
        match v {
            Value::Num(_) => true,
            _ => false,
        }
    }

    // The catch-all sits beside a NESTED constructor pattern.
    #[val]
    fn head_num(xs: VList) -> Nat {
        match xs {
            VList::VCons(Value::Num(n), _) => n,
            _ => Nat::Z,
        }
    }

    // The scrutinee may be used in the catch-all body.
    #[val]
    fn pred_or_self(x: Nat) -> Nat {
        match x {
            Nat::S(m) => *m,
            _ => x,
        }
    }

    #[val((b: bool) -> Lemma(is_num(Value::BoolV(b)) == false))]
    fn is_num_bool(b: bool) {}

    #[val((b: bool) -> Lemma(is_num(Value::Unit0) == false))]
    fn is_num_unit(b: bool) {}

    #[val((n: Nat, t: VList) -> Lemma(head_num(VList::VCons(Value::Num(n), t)) == n))]
    fn head_num_hit(n: Nat, t: VList) {}

    #[val((b: bool, t: VList) -> Lemma(head_num(VList::VCons(Value::BoolV(b), t)) == Nat::Z))]
    fn head_num_bool(b: bool, t: VList) {}

    #[val((b: bool) -> Lemma(head_num(VList::VNil) == Nat::Z))]
    fn head_num_nil(b: bool) {}

    #[val((b: bool) -> Lemma(pred_or_self(Nat::Z) == Nat::Z))]
    fn pred_or_self_z(b: bool) {}

    // A catch-all in a PROOF body: one VC per constructor it stands for.
    #[val((v: Value, t: VList) -> Lemma(implies(is_num(v) == false, head_num(VList::VCons(v, t)) == Nat::Z)))]
    fn head_num_non_num(v: Value, t: VList) {
        match v {
            Value::Num(n) => (),
            _ => (),
        }
    }
}
