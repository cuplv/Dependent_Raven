// TIP IsaPlanner prop_47: height(mirror(t)) == height(t)
//
// Lemma-gap fixture: the instantiate procedure has already run to
// saturation on this proof -- the third hint below (the swapped max) is
// its work -- and the verification still fails. Both induction
// hypotheses are present. The missing piece is a FACT, not a term.
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

    #[val((t: Tree) -> Lemma(height(mirror(t)) == height(t)))]
    #[allow(unused_variables)]
    fn tip_47(t: Tree) {
        match t {
            Tree::Leaf => (),
            Tree::Node(l, e, r) => {
                instantiate!(Tree::Node(Box::new(mirror(r)), e, Box::new(mirror(l))));
                instantiate!(Nat::S(max(height(l), height(r))));
                instantiate!(Nat::S(max(height(mirror(r)), height(mirror(l)))));
                tip_47(*l.clone()); // induction hypothesis, left subtree
                tip_47(*r.clone()); // induction hypothesis, right subtree
            }
        }
    }
}
