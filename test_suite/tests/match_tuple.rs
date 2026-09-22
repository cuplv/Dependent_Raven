// `match (a, b) { .. }`: a match on a tuple of variables. At registration it is
// compiled into nested single-variable matches, trying the rows in source order
// (Rust's first-match semantics), so rows may overlap and end in a `_` row.
#[ravencheck::module]
mod match_tuple {

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
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Res {
        Done(Value),
        Fail,
    }

    #[val]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x1) => Nat::S(Box::new(add(*x1, y))),
        }
    }

    #[val]
    fn is_num(v: Value) -> bool {
        match v {
            Value::Num(_) => true,
            _ => false,
        }
    }

    // The stack-machine shape: both operands must be numbers.
    #[val]
    fn plus_vals(a: Value, b: Value) -> Res {
        match (a, b) {
            (Value::Num(x), Value::Num(y)) => Res::Done(Value::Num(add(x, y))),
            _ => Res::Fail,
        }
    }

    // Overlapping rows and a variable binder: the FIRST matching row wins.
    #[val]
    fn pick(a: Value, b: Value) -> Value {
        match (a, b) {
            (Value::Num(x), _) => Value::Num(x),
            (_, Value::Num(y)) => Value::Num(y),
            (first, _) => first,
        }
    }

    #[val((x: Nat, y: Nat) -> Lemma(plus_vals(Value::Num(x), Value::Num(y)) == Res::Done(Value::Num(add(x, y)))))]
    fn plus_vals_nums(x: Nat, y: Nat) {}

    #[val((p: bool, v: Value) -> Lemma(plus_vals(Value::BoolV(p), v) == Res::Fail))]
    fn plus_vals_bool_left(p: bool, v: Value) {
        match v {
            Value::Num(n) => (),
            _ => (),
        }
    }

    #[val((x: Nat, p: bool) -> Lemma(plus_vals(Value::Num(x), Value::BoolV(p)) == Res::Fail))]
    fn plus_vals_bool_right(x: Nat, p: bool) {}

    #[val((x: Nat, y: Nat) -> Lemma(pick(Value::Num(x), Value::Num(y)) == Value::Num(x)))]
    fn pick_first_row_wins(x: Nat, y: Nat) {}

    #[val((p: bool, y: Nat) -> Lemma(pick(Value::BoolV(p), Value::Num(y)) == Value::Num(y)))]
    fn pick_second_row(p: bool, y: Nat) {}

    #[val((p: bool, q: bool) -> Lemma(pick(Value::BoolV(p), Value::BoolV(q)) == Value::BoolV(p)))]
    fn pick_binder_row(p: bool, q: bool) {}

    // A tuple match in a PROOF body: one VC per leaf of the compiled matches.
    #[val((a: Value, b: Value) -> Lemma(implies(is_num(a) && is_num(b), plus_vals(a, b) != Res::Fail)))]
    fn plus_vals_defined(a: Value, b: Value) {
        match (a, b) {
            (Value::Num(x), Value::Num(y)) => {
                instantiate!(Res::Done(Value::Num(add(x, y))));
            }
            _ => (),
        }
    }
}
