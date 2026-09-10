// Nested constructor patterns that are pairwise DISJOINT must still be
// accepted by the overlap check: the two Node arms differ in their first field.
// (The nested field is an unboxed Nat, since Rust cannot pattern-match through
// a Box; the module must still compile as ordinary Rust.)
#[ravencheck::module]
mod match_disjoint {

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
        Node(Nat, Box<Tree>),
    }

    #[val]
    fn root_is_zero(t: Tree) -> bool {
        match t {
            Tree::Leaf => false,
            Tree::Node(Nat::Z, _) => true,
            Tree::Node(Nat::S(_), _) => false,
        }
    }

    #[val((r: Tree) -> Lemma(root_is_zero(Tree::Node(Nat::Z, Box::new(r)))))]
    fn zero_root_is_detected(r: Tree) {}

    #[val((n: Nat, r: Tree) -> Lemma(!root_is_zero(Tree::Node(Nat::S(Box::new(n)), Box::new(r)))))]
    fn succ_root_is_not_zero(n: Nat, r: Tree) {}
}
