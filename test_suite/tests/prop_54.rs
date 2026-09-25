// TIP IsaPlanner prop_54: sub(add(m, n), n) == m
//
// The minimal genuinely multi-helper Nat proof: induction on n, leaning on
// THREE helpers -- add_zero and sub_zero close the base case (add matches
// on its first argument, so add(m, Z) needs its own induction), and
// add_succ_r rewrites add(m, S(n')) to S(add(m, n')) so sub's S-S equation
// can step in the inductive case.
#[ravencheck::module]
mod tip_benchmarks {

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

    #[val]
    #[recursive]
    fn sub(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => Nat::Z,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => sub(*x_min, *y_min),
            },
        }
    }

    // Helper: sub(x, Z) == x. Both shapes of x close definitionally.
    #[val((x: Nat) -> Lemma(sub(x, Nat::Z) == x))]
    #[allow(unused_variables)]
    fn sub_zero(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(_x_min) => (),
        }
    }

    // Helper: add(x, Z) == x.
    #[val((x: Nat) -> Lemma(add(x, Nat::Z) == x))]
    fn add_zero(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                add_zero(*x_min)
            }
        }
    }

    // Helper: add(x, S(y)) == S(add(x, y)).
    #[val((x: Nat, y: Nat) -> Lemma(add(x, Nat::S(Box::new(y))) == Nat::S(Box::new(add(x, y)))))]
    fn add_succ_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                add_succ_r(*x_min, y)
            }
        }
    }

    #[val((m: Nat, n: Nat) -> Lemma(sub(add(m, n), n) == m))]
    fn tip_54(m: Nat, n: Nat) {
        match n {
            Nat::Z => {
                add_zero(m.clone());
                sub_zero(m)
            }
            Nat::S(n_min) => {
                add_succ_r(m.clone(), *n_min.clone());
                tip_54(m, *n_min)
            }
        }
    }
}
