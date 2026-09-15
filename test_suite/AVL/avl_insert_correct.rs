// Trial file: the AVL specification (identical to avl_spec.rs) plus the
// COMBINED target theorem with its induction skeleton and nothing else -- no
// helper lemmas, no hints. The two F* theorems (insert_preserves_balance,
// insert_height_bound) are not provable separately: each Node case needs the
// other's conclusion on the subtree, so the recursive call must carry both.
// Copy into tests/ to work on it; this file itself is never edited during a trial.
#[ravencheck::module]
mod avl_insert_correct {

    // Recursive Nat type
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    // leq operator
    #[val]
    #[recursive]
    fn leq(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => true,
            Nat::S(x1) => match y {
                Nat::Z => false,
                Nat::S(y1) => leq(*x1, *y1),
            },
        }
    }

    #[val]
    #[recursive]
    fn lt(x: Nat, y: Nat) -> bool {
        match y {
            Nat::Z => false,
            Nat::S(y1) => match x {
                Nat::Z => true,
                Nat::S(x1) => lt(*x1, *y1),
            },
        }
    }

    #[val]
    #[recursive]
    fn eq_nat(x: Nat, y: Nat) -> bool {
        match x {
            Nat::Z => match y {
                Nat::Z => true,
                Nat::S(_) => false,
            },
            Nat::S(x1) => match y {
                Nat::Z => false,
                Nat::S(y1) => eq_nat(*x1, *y1),
            },
        }
    }

    #[val]
    #[recursive]
    fn max(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x1) => match y {
                Nat::Z => Nat::S(x1),
                Nat::S(y1) => Nat::S(Box::new(max(*x1, *y1))),
            },
        }
    }

    // Tree datatype:  Node(left, value, height, right)
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Tree {
        Leaf,
        Node(Box<Tree>, Nat, Nat, Box<Tree>),
    }

    // height function
    #[val]
    fn height(t: Tree) -> Nat {
        match t {
            Tree::Leaf => Nat::Z,
            Tree::Node(_, _, h, _) => h,
        }
    }

    #[val]
    fn node(l: Tree, v: Nat, r: Tree) -> Tree {
        Tree::Node(
            Box::new(l.clone()),
            v,
            Nat::S(Box::new(max(height(l), height(r.clone())))),
            Box::new(r),
        )
    }

    // is_balanced predicate
    #[val]
    #[recursive]
    fn is_balanced(t: Tree) -> bool {
        match t {
            Tree::Leaf => true,
            Tree::Node(l, _, h, r) => {
                let hl = height(*l.clone());
                let hr = height(*r.clone());
                leq(hl.clone(), Nat::S(Box::new(hr.clone())))
                    && leq(hr.clone(), Nat::S(Box::new(hl.clone())))
                    && eq_nat(h, Nat::S(Box::new(max(hl, hr))))
                    && is_balanced(*l)
                    && is_balanced(*r)
            }
        }
    }

    // Rotation operation: left and right
    #[val]
    fn rotate_right(l: Tree, v: Nat, r: Tree) -> Tree {
        match l {
            Tree::Node(ll, lv, _, lr) => {
                if leq(height(*lr.clone()), height(*ll.clone())) {
                    node(*ll, lv, node(*lr, v, r))
                } else {
                    match *lr {
                        Tree::Node(lrl, lrv, _, lrr) => {
                            node(node(*ll, lv, *lrl), lrv, node(*lrr, v, r))
                        }
                        Tree::Leaf => Tree::Leaf,
                    }
                }
            }
            Tree::Leaf => Tree::Leaf,
        }
    }

    #[val]
    fn rotate_left(l: Tree, v: Nat, r: Tree) -> Tree {
        match r {
            Tree::Node(rl, rv, _, rr) => {
                if leq(height(*rl.clone()), height(*rr.clone())) {
                    node(node(l, v, *rl), rv, *rr)
                } else {
                    match *rl {
                        Tree::Node(rll, rlv, _, rlr) => {
                            node(node(l, v, *rll), rlv, node(*rlr, rv, *rr))
                        }
                        Tree::Leaf => Tree::Leaf,
                    }
                }
            }
            Tree::Leaf => Tree::Leaf,
        }
    }

    // Function for balancing the tree
    #[val]
    fn balance(l: Tree, v: Nat, r: Tree) -> Tree {
        let hl = height(l.clone());
        let hr = height(r.clone());
        if leq(Nat::S(Box::new(Nat::S(Box::new(hr.clone())))), hl.clone()) {
            rotate_right(l, v, r)
        } else if leq(Nat::S(Box::new(Nat::S(Box::new(hl)))), hr) {
            rotate_left(l, v, r)
        } else {
            node(l, v, r)
        }
    }

    // Insert operation
    #[val]
    #[recursive]
    fn insert(x: Nat, t: Tree) -> Tree {
        match t.clone() {
            Tree::Leaf => Tree::Node(
                Box::new(Tree::Leaf),
                x,
                Nat::S(Box::new(Nat::Z)),
                Box::new(Tree::Leaf),
            ),
            Tree::Node(l, v, _, r) => {
                if lt(x.clone(), v.clone()) {
                    balance(insert(x, *l), v, *r)
                } else if lt(v.clone(), x.clone()) {
                    balance(*l, v, insert(x, *r))
                } else {
                    t
                }
            }
        }
    }

    // ---- target theorem ---------------------
    // let rec insert_correct (x: int) (t: tree)
    //   : Lemma (requires is_balanced t)
    //           (ensures is_balanced (insert x t) /\
    //                    (height (insert x t) == height t \/ height (insert x t) == height t + 1))
    #[val((x: Nat, t: Tree) -> Lemma(requires(is_balanced(t)), ensures(
        is_balanced(insert(x, t))
            && (height(insert(x, t)) == height(t)
                || height(insert(x, t)) == Nat::S(Box::new(height(t)))))))]
    fn insert_correct(x: Nat, t: Tree) {
        match t {
            Tree::Leaf => (),
            Tree::Node(l, v, _, r) => {
                if lt(x.clone(), v.clone()) {
                    insert_correct(x, *l);
                } else if lt(v.clone(), x.clone()) {
                    insert_correct(x, *r);
                } else {
                    ()
                }
            }
        }
    }
}
