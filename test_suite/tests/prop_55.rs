// TIP IsaPlanner prop_55:
//   drop(n, app(xs, ys)) == app(drop(n, xs), drop(sub(n, len(xs)), ys))
//
// Induction on n with a case split on xs; hint-free. Every function in the
// step recurses on an argument the branch fixes (n, xs, len(Cons(h, t))),
// so the peephole pins each result and the S/Cons case is the induction
// hypothesis at (n', t, ys).
#[ravencheck::module]
mod tip_benchmarks {

    // Uninterpreted element sort (the benchmark is polymorphic in `a`).
    #[declare]
    type Elem = u32;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum List {
        Nil,
        Cons(Elem, Box<List>),
    }

    #[val]
    #[recursive]
    fn len(xs: List) -> Nat {
        match xs {
            List::Nil => Nat::Z,
            List::Cons(_h, t) => Nat::S(Box::new(len(*t))),
        }
    }

    #[val]
    #[recursive]
    fn drop(n: Nat, xs: List) -> List {
        match n {
            Nat::Z => xs,
            Nat::S(n_min) => match xs {
                List::Nil => List::Nil,
                List::Cons(_h, t) => drop(*n_min, *t),
            },
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

    #[val]
    #[recursive]
    fn app(x: List, y: List) -> List {
        match x {
            List::Nil => y,
            List::Cons(h, t) => List::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((n: Nat, xs: List, ys: List) ->
        Lemma(drop(n, app(xs, ys)) == app(drop(n, xs), drop(sub(n, len(xs)), ys))))]
    fn tip_55(n: Nat, xs: List, ys: List) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => match xs {
                List::Nil => (),
                List::Cons(_h, t) => {
                    tip_55(*n_min, *t, ys);
                }
            },
        }
    }
}
