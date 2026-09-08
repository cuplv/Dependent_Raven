// BST specification, translated from BSTspec.fst.
//
// is_bst(t) <==> sorted(inorder(t)
// Translation notes:
// - F*'s int with </<= becomes Nat with the recursive lt/le.
// - forall_tree (p: int -> bool) is higher-order; only two predicates are
//   ever passed (x < v and v < x), so it is defunctionalized into
//   all_lt(t, v) ("every value in t is below v") and all_gt(t, v).
// - && becomes nested ifs (the guarded-equation encoding).
//
// The two target lemmas carry structural induction skeletons only (the
// F* file has admit()); they are EXPECTED TO FAIL until proven -- they
// are the starting material for the instantiate/lemma skills.

// Proved from scratch, with 2 lemma skill calls and 1 instantiate skill call
// Implicitly, lemma skill called instantiation skill 5 times,
// So total 2 lemma skill call and 6 instantiation skill call

// 8 Lemmas to prove the theorem

#[ravencheck::module]
mod bst_spec {

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum NList {
        Nil,
        Cons(Nat, Box<NList>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Tree {
        Leaf,
        Node(Box<Tree>, Nat, Box<Tree>),
    }

    #[val]
    #[recursive]
    fn lt(x: Nat, y: Nat) -> bool {
        match y {
            Nat::Z => false,
            Nat::S(y_min) => match x {
                Nat::Z => true,
                Nat::S(x_min) => lt(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn le(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(x_min) => match y {
                Nat::Z => false,
                Nat::S(y_min) => le(*x_min, *y_min),
            },
        }
    }

    #[val]
    #[recursive]
    fn app(x: NList, y: NList) -> NList {
        match x {
            NList::Nil => y,
            NList::Cons(h, t) => NList::Cons(h, Box::new(app(*t, y))),
        }
    }

    // In-order traversal: inorder(l) @ (v :: inorder(r)).
    #[val]
    #[recursive]
    fn inorder(t: Tree) -> NList {
        match t {
            Tree::Leaf => NList::Nil,
            Tree::Node(l, v, r) => app(inorder(*l), NList::Cons(v, Box::new(inorder(*r)))),
        }
    }

    #[val]
    #[recursive]
    fn sorted(xs: NList) -> bool {
        match xs {
            NList::Nil => true,
            NList::Cons(h, t) => match *t {
                NList::Nil => true,
                NList::Cons(h2, t2) => {
                    if le(h, h2.clone()) {
                        sorted(NList::Cons(h2, t2))
                    } else {
                        false
                    }
                }
            },
        }
    }

    // forall_tree (fun x -> x < v) t, defunctionalized.
    #[val]
    #[recursive]
    fn all_lt(t: Tree, v: Nat) -> bool {
        match t {
            Tree::Leaf => true,
            Tree::Node(l, x, r) => {
                if lt(x, v.clone()) {
                    if all_lt(*l, v.clone()) {
                        all_lt(*r, v)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    // forall_tree (fun x -> v < x) t, defunctionalized.
    #[val]
    #[recursive]
    fn all_gt(t: Tree, v: Nat) -> bool {
        match t {
            Tree::Leaf => true,
            Tree::Node(l, x, r) => {
                if lt(v.clone(), x) {
                    if all_gt(*l, v.clone()) {
                        all_gt(*r, v)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    // The BST invariant: strict bounds over WHOLE subtrees, recursively.
    #[val]
    #[recursive]
    fn is_bst(t: Tree) -> bool {
        match t {
            Tree::Leaf => true,
            Tree::Node(l, v, r) => {
                if all_lt(*l.clone(), v.clone()) {
                    if all_gt(*r.clone(), v) {
                        if is_bst(*l) {
                            is_bst(*r)
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    // Duplicate-free insert: equal keys are a no-op.
    #[val]
    #[recursive]
    fn insert(x: Nat, t: Tree) -> Tree {
        match t {
            Tree::Leaf => Tree::Node(Box::new(Tree::Leaf), x, Box::new(Tree::Leaf)),
            Tree::Node(l, v, r) => {
                if lt(x.clone(), v.clone()) {
                    Tree::Node(Box::new(insert(x, *l)), v, r)
                } else if lt(v.clone(), x.clone()) {
                    Tree::Node(l, v, Box::new(insert(x, *r)))
                } else {
                    Tree::Node(l, v, r)
                }
            }
        }
    }

    // Helper: the strict order implies the non-strict one.
    #[val((x: Nat, y: Nat) -> Lemma(implies(lt(x, y), le(x, y))))]
    fn lt_le(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => lt_le(*x_min, *y_min),
            },
        }
    }

    // Helper: append is associative.
    #[val((x: NList, y: NList, z: NList) -> Lemma(app(app(x, y), z) == app(x, app(y, z))))]
    fn app_assoc(x: NList, y: NList, z: NList) {
        match x {
            NList::Nil => (),
            NList::Cons(h, t) => {
                instantiate!(NList::Cons(h, app(t, y)));
                instantiate!(NList::Cons(h, app(t, app(y, z))));
                app_assoc(*t, y, z);
            }
        }
    }

    // Helper: both halves of a sorted append are sorted.
    #[val((xs: NList, ys: NList) -> Lemma(implies(sorted(app(xs, ys)), sorted(xs) && sorted(ys))))]
    fn split_sorted(xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(a, xs1) => match *xs1.clone() {
                NList::Nil => match ys.clone() {
                    NList::Nil => (),
                    NList::Cons(b, ys1) => {
                        instantiate!(NList::Cons(a, app(xs1, ys)));
                        instantiate!(le(a, b));
                    }
                },
                NList::Cons(b, xs2) => {
                    instantiate!(NList::Cons(a, app(xs1, ys)));
                    instantiate!(NList::Cons(b, app(xs2, ys)));
                    instantiate!(le(a, b));
                    split_sorted(*xs1.clone(), ys.clone());
                }
            },
        }
    }

    // Helper: splicing a sorted tail behind the pivot. "Every element of xs is
    // at most v" is expressed, without a list-level bound predicate, as
    // sorted(app(xs, [v])).
    #[val((xs: NList, v: Nat, ys: NList) -> Lemma(implies(
        sorted(app(xs, NList::Cons(v, NList::Nil))) && sorted(NList::Cons(v, ys)),
        sorted(app(xs, NList::Cons(v, ys))))))]
    fn sorted_concat(xs: NList, v: Nat, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(a, xs1) => match *xs1.clone() {
                NList::Nil => {
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(v, NList::Nil))));
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(v, ys))));
                    instantiate!(le(a, v));
                    instantiate!(sorted(NList::Cons(v, NList::Nil)));
                }
                NList::Cons(b, xs2) => {
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(v, NList::Nil))));
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(v, ys))));
                    instantiate!(NList::Cons(b, app(xs2, NList::Cons(v, NList::Nil))));
                    instantiate!(NList::Cons(b, app(xs2, NList::Cons(v, ys))));
                    instantiate!(le(a, b));
                    sorted_concat(*xs1.clone(), v.clone(), ys.clone());
                }
            },
        }
    }

    // Helper: dropping everything after the pivot keeps the prefix sorted.
    #[val((xs: NList, y: Nat, ys: NList) -> Lemma(implies(
        sorted(app(xs, NList::Cons(y, ys))),
        sorted(app(xs, NList::Cons(y, NList::Nil))))))]
    fn truncate_sorted(xs: NList, y: Nat, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(a, xs1) => match *xs1.clone() {
                NList::Nil => {
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(y, ys))));
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(y, NList::Nil))));
                    instantiate!(le(a, y));
                    instantiate!(sorted(NList::Cons(y, NList::Nil)));
                }
                NList::Cons(b, xs2) => {
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(y, ys))));
                    instantiate!(NList::Cons(a, app(xs1, NList::Cons(y, NList::Nil))));
                    instantiate!(NList::Cons(b, app(xs2, NList::Cons(y, ys))));
                    instantiate!(NList::Cons(b, app(xs2, NList::Cons(y, NList::Nil))));
                    instantiate!(le(a, b));
                    truncate_sorted(*xs1.clone(), y.clone(), ys.clone());
                }
            },
        }
    }

    // Helper: prefixing v onto app(xs, ys). Non-recursive -- the head of
    // app(xs, ys) is the head of xs when xs is a Cons, and ys otherwise.
    #[val((v: Nat, xs: NList, ys: NList) -> Lemma(implies(
        sorted(NList::Cons(v, xs)) && sorted(app(xs, ys)) && sorted(NList::Cons(v, ys)),
        sorted(NList::Cons(v, app(xs, ys))))))]
    fn cons_head(v: Nat, xs: NList, ys: NList) {
        match xs {
            NList::Nil => (),
            NList::Cons(a, xs1) => {
                instantiate!(NList::Cons(a, app(xs1, ys)));
                instantiate!(le(v, a));
            }
        }
    }

    // Helper: if v is strictly below every key of t, it can be prefixed onto
    // t's in-order traversal. Recursion keeps the pivot v FIXED and shrinks the
    // tree; the sub-facts about x and r are extracted from sorted(inorder(t))
    // by the list lemmas rather than by a recursive call at a new pivot.
    #[val((t: Tree, v: Nat) -> Lemma(implies(
        is_bst(t) && all_gt(t, v) && sorted(inorder(t)),
        sorted(NList::Cons(v, inorder(t))))))]
    fn bound_below(t: Tree, v: Nat) {
        match t {
            Tree::Leaf => (),
            Tree::Node(l, x, r) => {
                instantiate!(all_gt(r, v));
                instantiate!(is_bst(l));
                instantiate!(all_lt(l, x));
                instantiate!(all_gt(r, x));
                split_sorted(
                    inorder(*l.clone()),
                    NList::Cons(x.clone(), Box::new(inorder(*r.clone()))),
                );
                lt_le(v.clone(), x.clone());
                bound_below(*l.clone(), v.clone());
                cons_head(
                    v.clone(),
                    inorder(*l.clone()),
                    NList::Cons(x.clone(), Box::new(inorder(*r.clone()))),
                );
            }
        }
    }

    // Helper: mirror of bound_below -- if v is strictly above every key of t,
    // it can be appended to t's in-order traversal. Recursion is on the RIGHT
    // subtree with v fixed; the left part is handled by truncate_sorted, which
    // is what avoids a recursive call at the new pivot x.
    #[val((t: Tree, v: Nat) -> Lemma(implies(
        is_bst(t) && all_lt(t, v) && sorted(inorder(t)),
        sorted(app(inorder(t), NList::Cons(v, NList::Nil))))))]
    fn bound_above(t: Tree, v: Nat) {
        match t {
            Tree::Leaf => (),
            Tree::Node(l, x, r) => {
                instantiate!(all_lt(l, v));
                instantiate!(is_bst(l));
                instantiate!(all_lt(l, x));
                instantiate!(all_gt(r, x));
                instantiate!(sorted(NList::Cons(v, NList::Nil)));
                instantiate!(NList::Cons(x, app(NList::Nil, inorder(r))));
                split_sorted(
                    inorder(*l.clone()),
                    NList::Cons(x.clone(), Box::new(inorder(*r.clone()))),
                );
                split_sorted(
                    NList::Cons(x.clone(), Box::new(NList::Nil)),
                    inorder(*r.clone()),
                );
                truncate_sorted(inorder(*l.clone()), x.clone(), inorder(*r.clone()));
                lt_le(x.clone(), v.clone());
                bound_above(*r.clone(), v.clone());
                app_assoc(
                    inorder(*l.clone()),
                    NList::Cons(x.clone(), Box::new(inorder(*r.clone()))),
                    NList::Cons(v.clone(), Box::new(NList::Nil)),
                );
                cons_head(
                    x.clone(),
                    inorder(*r.clone()),
                    NList::Cons(v.clone(), Box::new(NList::Nil)),
                );
                sorted_concat(
                    inorder(*l.clone()),
                    x.clone(),
                    app(
                        inorder(*r.clone()),
                        NList::Cons(v.clone(), Box::new(NList::Nil)),
                    ),
                );
            }
        }
    }

    // Proposition 1: is_bst(t) ==> sorted(inorder(t)).
    #[val((t: Tree) -> Lemma(requires(is_bst(t)), ensures(sorted(inorder(t)))))]
    #[allow(unused_variables)]
    fn bst_inorder_sorted(t: Tree) {
        match t {
            Tree::Leaf => (),
            Tree::Node(l, v, r) => {
                instantiate!(all_lt(l, v));
                instantiate!(all_gt(r, v));
                instantiate!(is_bst(l));
                sorted_concat(inorder(*l.clone()), v.clone(), inorder(*r.clone()));
                bst_inorder_sorted(*l.clone());
                bst_inorder_sorted(*r.clone());
                bound_above(*l.clone(), v.clone());
                bound_below(*r.clone(), v.clone());
            }
        }
    }
}
