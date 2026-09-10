// Wildcards nested inside constructor patterns, in a function body and in a
// proof body. Each `_` becomes a fresh binder the checker and the axiom
// generator can name; previously it panicked in `pattern_to_expr`.
#[ravencheck::module]
mod wildcard_pattern {

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
        Node(Box<Tree>, Nat, Box<Tree>),
    }

    #[val]
    fn root_or_z(t: Tree) -> Nat {
        match t {
            Tree::Leaf => Nat::Z,
            Tree::Node(_, v, _) => v,
        }
    }

    #[val]
    fn is_leaf(t: Tree) -> bool {
        match t {
            Tree::Leaf => true,
            Tree::Node(_, _, _) => false,
        }
    }

    #[val((l: Tree, v: Nat, r: Tree) -> Lemma(root_or_z(Tree::Node(Box::new(l), v, Box::new(r))) == v))]
    fn root_of_node(l: Tree, v: Nat, r: Tree) {}

    #[val((t: Tree) -> Lemma(implies(is_leaf(t), root_or_z(t) == Nat::Z)))]
    fn leaf_root_is_z(t: Tree) {
        match t {
            Tree::Leaf => (),
            Tree::Node(_, _, _) => (),
        }
    }
}
