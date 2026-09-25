// TIP IsaPlanner prop_47: height(mirror(t)) == height(t)
//
// The only tree property in the benchmark set, and the canonical proof that
// needs SEVERAL facts in one branch: the Node case invokes the induction
// hypothesis on the left subtree, the induction hypothesis on the right
// subtree, and the commutativity of max -- three sequenced calls.
#[ravencheck::module]
mod tip_benchmarks {

    // Tree elements: an uninterpreted sort (u32 at runtime).
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
    pub enum Tree {
        Leaf,
        Node(Box<Tree>, Elem, Box<Tree>),
    }

    #[val]
    #[recursive]
    fn max(x: Nat, y: Nat) -> Nat {
        match x.clone() {
            Nat::Z => y,
            Nat::S(x_min) => match y {
                Nat::Z => x,
                Nat::S(y_min) => Nat::S(Box::new(max(*x_min, *y_min))),
            },
        }
    }

    #[val]
    #[recursive]
    fn height(t: Tree) -> Nat {
        match t {
            Tree::Leaf => Nat::Z,
            Tree::Node(l, _e, r) => Nat::S(Box::new(max(height(*l), height(*r)))),
        }
    }

    #[val]
    #[recursive]
    fn mirror(t: Tree) -> Tree {
        match t {
            Tree::Leaf => Tree::Leaf,
            Tree::Node(l, e, r) => Tree::Node(Box::new(mirror(*r)), e, Box::new(mirror(*l))),
        }
    }

    // Helper: max is commutative (same proof as prop_23).
    #[val((a: Nat, b: Nat) -> Lemma(max(a, b) == max(b, a)))]
    fn max_comm(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    max_comm(*a_min, *b_min);
                }
            },
        }
    }

    #[val((t: Tree) -> Lemma(height(mirror(t)) == height(t)))]
    #[allow(unused_variables)]
    fn tip_47(t: Tree) {
        match t {
            Tree::Leaf => (),
            Tree::Node(l, e, r) => {
                // The mirrored node and the wrapped max are the intermediate
                // values of unfolding the definitions; naming them here makes
                // them available to the solver.

                tip_47(*l.clone()); // induction hypothesis, left subtree
                tip_47(*r.clone()); // induction hypothesis, right subtree
                max_comm(height(*l), height(*r))
            }
        }
    }
}
