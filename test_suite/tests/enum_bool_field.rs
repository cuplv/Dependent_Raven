// A `bool` field in a `#[define]` enum is the solver's built-in Bool, as it
// already is in function signatures. Previously the field was registered as an
// undeclared custom sort named "bool" and the checker panicked on the mismatch.
#[ravencheck::module]
mod enum_bool_field {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Value {
        BoolV(bool),
        NumV(Nat),
    }

    // A bool field bound by a pattern is returned as a Bool.
    #[val]
    fn is_true(v: Value) -> bool {
        match v {
            Value::BoolV(b) => b,
            Value::NumV(_) => false,
        }
    }

    // A bool field is rebuilt from a Bool expression.
    #[val]
    fn negate(v: Value) -> Value {
        match v {
            Value::BoolV(b) => Value::BoolV(!b),
            Value::NumV(n) => Value::NumV(n),
        }
    }

    #[val((v: Value) -> Lemma(is_true(Value::BoolV(true))))]
    fn is_true_of_true(v: Value) {}

    // Constructor injectivity on a Bool field.
    #[val((a: bool, b: bool) -> Lemma(implies(Value::BoolV(a) == Value::BoolV(b), a == b)))]
    fn boolv_injective(a: bool, b: bool) {}

    #[val((v: Value) -> Lemma(negate(negate(v)) == v))]
    fn negate_involutive(v: Value) {
        match v {
            Value::BoolV(b) => {
                instantiate!(Value::BoolV(!b));
            }
            Value::NumV(n) => (),
        }
    }
}
