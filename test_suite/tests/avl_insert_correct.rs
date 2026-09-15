// Trial file: the AVL specification (identical to avl_spec.rs) plus the
// COMBINED target theorem with its induction skeleton and nothing else -- no
// helper lemmas, no hints. The two F* theorems (insert_preserves_balance,
// insert_height_bound) are not provable separately: each Node case needs the
// other's conclusion on the subtree, so the recursive call must carry both.
// Copy into tests/ to work on it; this file itself is never edited during a trial.

// Proved with 22 lemmas and 285 instantiations..
// The number of call: Total 2 times of lemma skill call
// and 18 times of instantiation skill call(implicity instantiation skill call: 16 times)
// Explicit call means call by user's prompt, implicit means call by other skill(in this case, lemma skill)

// ---- target theorem ---------------------
// let rec insert_correct (x: int) (t: tree)
//   : Lemma (requires is_balanced t)
//           (ensures is_balanced (insert x t) /\
//                    (height (insert x t) == height t \/ height (insert x t) == height t + 1))
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

    // Helper: eq_nat is reflexive.
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_nat_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_nat_refl(*x_min),
        }
    }

    // Helper: eq_nat implies equality.
    #[val((a: Nat, b: Nat) -> Lemma(implies(eq_nat(a, b), a == b)))]
    fn eq_nat_eq(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    eq_nat_eq(*a_min, *b_min);
                }
            },
        }
    }

    // Helper: b <= S(a) rules out S(S(a)) <= b.
    #[val((a: Nat, b: Nat) -> Lemma(implies(leq(b, Nat::S(Box::new(a))), !leq(Nat::S(Box::new(Nat::S(Box::new(a)))), b))))]
    fn leq_contra(a: Nat, b: Nat) {
        match b {
            Nat::Z => (),
            Nat::S(b_min) => match a {
                Nat::Z => {
                    instantiate!(leq(b_min, a));
                    instantiate!(leq(Nat::S(a), b_min));
                    match *b_min {
                        Nat::Z => (),
                        Nat::S(_b_min_min) => (),
                    }
                }
                Nat::S(a_min) => {
                    leq_contra(*a_min, *b_min);
                }
            },
        }
    }

    // Helper: Z is a right identity of max.
    #[val((x: Nat) -> Lemma(max(x, Nat::Z) == x))]
    fn max_zero_r(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(_x_min) => (),
        }
    }

    // Helper: S(x) <= y implies x <= y.
    #[val((x: Nat, y: Nat) -> Lemma(implies(leq(Nat::S(Box::new(x)), y), leq(x, y))))]
    fn leq_succ_l(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    leq_succ_l(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: x <= y implies x <= S(y).
    #[val((x: Nat, y: Nat) -> Lemma(implies(leq(x, y), leq(x, Nat::S(Box::new(y))))))]
    fn leq_succ_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    leq_succ_r(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: leq is transitive.
    #[val((x: Nat, y: Nat, z: Nat) -> Lemma(implies(leq(x, y) && leq(y, z), leq(x, z))))]
    fn leq_trans(x: Nat, y: Nat, z: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => match z {
                    Nat::Z => (),
                    Nat::S(z_min) => {
                        leq_trans(*x_min, *y_min, *z_min);
                    }
                },
            },
        }
    }

    // Helper: y <= x implies max(x, y) == x.
    #[val((x: Nat, y: Nat) -> Lemma(implies(leq(y, x), max(x, y) == x)))]
    fn max_leq(x: Nat, y: Nat) {
        match x {
            Nat::Z => match y {
                Nat::Z => (),
                Nat::S(_y_min) => (),
            },
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    max_leq(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: not S(a) <= b implies b <= a.
    #[val((a: Nat, b: Nat) -> Lemma(implies(!leq(Nat::S(Box::new(a)), b), leq(b, a))))]
    fn leq_neg_strong(a: Nat, b: Nat) {
        match b {
            Nat::Z => (),
            Nat::S(b_min) => match a {
                Nat::Z => {
                    instantiate!(leq(a, b_min));
                }
                Nat::S(a_min) => {
                    leq_neg_strong(*a_min, *b_min);
                }
            },
        }
    }

    // Helper: max(S(x), y) is max(x, y) or S(max(x, y)).
    #[val((x: Nat, y: Nat) -> Lemma(max(Nat::S(Box::new(x)), y) == max(x, y)
        || max(Nat::S(Box::new(x)), y) == Nat::S(Box::new(max(x, y)))))]
    fn max_succ_l(x: Nat, y: Nat) {
        match x {
            Nat::Z => match y {
                Nat::Z => (),
                Nat::S(_y_min) => {
                    instantiate!(Nat::S(max(x, _y_min)));
                }
            },
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    max_succ_l(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: x <= y implies max(x, y) == y.
    #[val((x: Nat, y: Nat) -> Lemma(implies(leq(x, y), max(x, y) == y)))]
    fn max_leq_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    max_leq_r(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: b <= a <= S(b) implies a is b or S(b).
    #[val((a: Nat, b: Nat) -> Lemma(implies(leq(b, a) && leq(a, Nat::S(Box::new(b))),
        a == b || a == Nat::S(Box::new(b)))))]
    fn leq_antisym_succ(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => {
                    instantiate!(leq(a_min, b));
                    match *a_min {
                        Nat::Z => (),
                        Nat::S(_a_min_min) => (),
                    }
                }
                Nat::S(b_min) => {
                    leq_antisym_succ(*a_min, *b_min);
                }
            },
        }
    }

    // Helper: not x <= y implies S(y) <= x.
    #[val((x: Nat, y: Nat) -> Lemma(implies(!leq(x, y), leq(Nat::S(Box::new(y)), x))))]
    fn leq_neg_lt(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => {
                    instantiate!(leq(y, x_min));
                }
                Nat::S(y_min) => {
                    leq_neg_lt(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: leq is antisymmetric.
    #[val((x: Nat, y: Nat) -> Lemma(implies(leq(x, y) && leq(y, x), x == y)))]
    fn leq_antisym(x: Nat, y: Nat) {
        match x {
            Nat::Z => match y {
                Nat::Z => (),
                Nat::S(_y_min) => (),
            },
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    leq_antisym(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: x <= max(x, y).
    #[val((x: Nat, y: Nat) -> Lemma(leq(x, max(x, y))))]
    fn leq_max_l(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => {
                    instantiate!(leq(x_min, x_min));
                    leq_max_l(*x_min.clone(), y.clone());
                    max_zero_r(*x_min.clone());
                }
                Nat::S(y_min) => {
                    instantiate!(Nat::S(max(x_min, y_min)));
                    leq_max_l(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: leq is reflexive.
    #[val((x: Nat) -> Lemma(leq(x, x)))]
    fn leq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => leq_refl(*x_min),
        }
    }

    // Helper: y <= max(x, y).
    #[val((x: Nat, y: Nat) -> Lemma(leq(y, max(x, y))))]
    fn leq_max_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => {
                leq_refl(y.clone());
            }
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => {
                    instantiate!(Nat::S(max(x_min, y_min)));
                    leq_max_r(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: x <= S(x).
    #[val((x: Nat) -> Lemma(leq(x, Nat::S(Box::new(x)))))]
    fn leq_succ_self(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => leq_succ_self(*x_min),
        }
    }

    // Helper: x <= z and y <= z imply max(x, y) <= z.
    #[val((x: Nat, y: Nat, z: Nat) -> Lemma(implies(leq(x, z) && leq(y, z), leq(max(x, y), z))))]
    fn max_bound(x: Nat, y: Nat, z: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => (),
                Nat::S(y_min) => match z {
                    Nat::Z => (),
                    Nat::S(z_min) => {
                        instantiate!(Nat::S(max(x_min, y_min)));
                        max_bound(*x_min, *y_min, *z_min);
                    }
                },
            },
        }
    }

    // Helper: rebalancing after the left subtree grew by at most one keeps
    // the tree balanced, with height h or S(h).
    #[val((l: Tree, v: Nat, h: Nat, r: Tree, l2: Tree) -> Lemma(implies(
        is_balanced(Tree::Node(Box::new(l), v, h, Box::new(r)))
            && is_balanced(l2)
            && (height(l2) == height(l) || height(l2) == Nat::S(Box::new(height(l)))),
        is_balanced(balance(l2, v, r))
            && (height(balance(l2, v, r)) == h
                || height(balance(l2, v, r)) == Nat::S(Box::new(h))))))]
    fn bal_left(l: Tree, v: Nat, h: Nat, r: Tree, l2: Tree) {
        match l2.clone() {
            Tree::Leaf => {
                instantiate!(leq(height(l), Nat::S(height(r))));
                instantiate!(leq(height(r), Nat::S(height(l))));
                instantiate!(eq_nat(h, Nat::S(max(height(l), height(r)))));
                instantiate!(is_balanced(l));
                instantiate!(is_balanced(r));
                instantiate!(leq(Nat::S(Nat::S(height(r))), height(l2)));
                instantiate!(rotate_right(l2, v, r));
                instantiate!(leq(Nat::S(Nat::S(height(l2))), height(r)));
                instantiate!(rotate_left(l2, v, r));
                instantiate!(node(l2, v, r));
                instantiate!(Tree::Node(l2, v, Nat::S(max(height(l2), height(r))), r));
                instantiate!(leq(height(l2), Nat::S(height(r))));
                instantiate!(leq(height(r), Nat::S(height(l2))));
                instantiate!(eq_nat(
                    Nat::S(max(height(l2), height(r))),
                    Nat::S(max(height(l2), height(r)))
                ));
                instantiate!(eq_nat(
                    max(height(l2), height(r)),
                    max(height(l2), height(r))
                ));
                eq_nat_refl(max(height(l2.clone()), height(r.clone())));
                leq_contra(height(l2.clone()), height(r.clone()));
                eq_nat_eq(
                    h.clone(),
                    Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                );
            }
            Tree::Node(_ll, _lv, _lh, lr) => match *lr.clone() {
                Tree::Leaf => {
                    instantiate!(leq(height(l), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l))));
                    instantiate!(eq_nat(h, Nat::S(max(height(l), height(r)))));
                    instantiate!(is_balanced(l));
                    instantiate!(is_balanced(r));
                    instantiate!(leq(height(_ll), Nat::S(height(lr))));
                    instantiate!(leq(height(lr), Nat::S(height(_ll))));
                    instantiate!(eq_nat(_lh, Nat::S(max(height(_ll), height(lr)))));
                    instantiate!(is_balanced(_ll));
                    instantiate!(is_balanced(lr));
                    instantiate!(leq(Nat::S(Nat::S(height(r))), height(l2)));
                    instantiate!(rotate_right(l2, v, r));
                    instantiate!(leq(Nat::S(Nat::S(height(l2))), height(r)));
                    instantiate!(rotate_left(l2, v, r));
                    instantiate!(node(l2, v, r));
                    instantiate!(leq(height(lr), height(_ll)));
                    instantiate!(node(_ll, _lv, node(lr, v, r)));
                    instantiate!(Tree::Node(l2, v, Nat::S(max(height(l2), height(r))), r));
                    instantiate!(Tree::Node(
                        _ll,
                        _lv,
                        Nat::S(max(height(_ll), height(node(lr, v, r)))),
                        node(lr, v, r)
                    ));
                    instantiate!(Tree::Node(lr, v, Nat::S(max(height(lr), height(r))), r));
                    instantiate!(leq(height(l2), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l2))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(l2), height(r))),
                        Nat::S(max(height(l2), height(r)))
                    ));
                    instantiate!(leq(height(_ll), Nat::S(height(node(lr, v, r)))));
                    instantiate!(leq(height(node(lr, v, r)), Nat::S(height(_ll))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(_ll), height(node(lr, v, r)))),
                        Nat::S(max(height(_ll), height(node(lr, v, r))))
                    ));
                    instantiate!(is_balanced(node(lr, v, r)));
                    instantiate!(eq_nat(
                        max(height(l2), height(r)),
                        max(height(l2), height(r))
                    ));
                    instantiate!(leq(max(height(lr), height(r)), height(_ll)));
                    instantiate!(eq_nat(
                        max(height(_ll), height(node(lr, v, r))),
                        max(height(_ll), height(node(lr, v, r)))
                    ));
                    instantiate!(leq(height(lr), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(lr))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(lr), height(r))),
                        Nat::S(max(height(lr), height(r)))
                    ));
                    instantiate!(eq_nat(
                        max(height(lr), height(r)),
                        max(height(lr), height(r))
                    ));
                    // G1 (rotate right)
                    eq_nat_eq(
                        _lh.clone(),
                        Nat::S(Box::new(max(height(*_ll.clone()), height(*lr.clone())))),
                    );
                    max_zero_r(height(*_ll.clone()));
                    leq_succ_l(height(r.clone()), height(*_ll.clone()));
                    leq_trans(
                        height(*_ll.clone()),
                        Nat::S(Box::new(height(*lr.clone()))),
                        Nat::S(Box::new(height(node(*lr.clone(), v.clone(), r.clone())))),
                    );
                    leq_trans(
                        height(r.clone()),
                        height(*_ll.clone()),
                        Nat::S(Box::new(height(*lr.clone()))),
                    );
                    eq_nat_refl(max(
                        height(*_ll.clone()),
                        height(node(*lr.clone(), v.clone(), r.clone())),
                    ));
                    eq_nat_refl(max(height(*lr.clone()), height(r.clone())));
                    max_leq(
                        height(*_ll.clone()),
                        height(node(*lr.clone(), v.clone(), r.clone())),
                    );
                    leq_contra(height(r.clone()), height(l.clone()));
                    max_leq(height(l.clone()), height(r.clone()));
                    leq_succ_l(height(r.clone()), height(l.clone()));
                    eq_nat_eq(
                        h.clone(),
                        Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                    );
                    // G2 (rotate left: impossible)
                    leq_succ_r(height(r.clone()), Nat::S(Box::new(height(l.clone()))));
                    leq_contra(height(l2.clone()), height(r.clone()));
                    // else (node)
                    leq_neg_strong(Nat::S(Box::new(height(r.clone()))), height(l2.clone()));
                    leq_neg_strong(Nat::S(Box::new(height(l2.clone()))), height(r.clone()));
                    eq_nat_refl(max(height(l2.clone()), height(r.clone())));
                    max_succ_l(height(l.clone()), height(r.clone()));
                }
                Tree::Node(_lrl, _lrv, _lrh, _lrr) => {
                    instantiate!(leq(height(l), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l))));
                    instantiate!(eq_nat(h, Nat::S(max(height(l), height(r)))));
                    instantiate!(is_balanced(l));
                    instantiate!(is_balanced(r));
                    instantiate!(leq(height(_ll), Nat::S(height(lr))));
                    instantiate!(leq(height(lr), Nat::S(height(_ll))));
                    instantiate!(eq_nat(_lh, Nat::S(max(height(_ll), height(lr)))));
                    instantiate!(is_balanced(_ll));
                    instantiate!(is_balanced(lr));
                    instantiate!(leq(Nat::S(Nat::S(height(r))), height(l2)));
                    instantiate!(rotate_right(l2, v, r));
                    instantiate!(leq(Nat::S(Nat::S(height(l2))), height(r)));
                    instantiate!(rotate_left(l2, v, r));
                    instantiate!(node(l2, v, r));
                    if leq(
                        Nat::S(Box::new(Nat::S(Box::new(height(r.clone()))))),
                        height(l2.clone()),
                    ) {
                        // G1 (rotate right)
                        instantiate!(leq(height(lr), height(_ll)));
                        if leq(height(*lr.clone()), height(*_ll.clone())) {
                            // single rotation
                            instantiate!(node(_ll, _lv, node(lr, v, r)));
                            instantiate!(Tree::Node(
                                _ll,
                                _lv,
                                Nat::S(max(height(_ll), height(node(lr, v, r)))),
                                node(lr, v, r)
                            ));
                            instantiate!(Tree::Node(lr, v, Nat::S(max(height(lr), height(r))), r));
                            instantiate!(leq(height(_ll), Nat::S(height(node(lr, v, r)))));
                            instantiate!(leq(height(node(lr, v, r)), Nat::S(height(_ll))));
                            instantiate!(eq_nat(
                                Nat::S(max(height(_ll), height(node(lr, v, r)))),
                                Nat::S(max(height(_ll), height(node(lr, v, r))))
                            ));
                            instantiate!(is_balanced(node(lr, v, r)));
                            instantiate!(leq(max(height(lr), height(r)), height(_ll)));
                            instantiate!(eq_nat(
                                max(height(_ll), height(node(lr, v, r))),
                                max(height(_ll), height(node(lr, v, r)))
                            ));
                            instantiate!(leq(height(lr), Nat::S(height(r))));
                            instantiate!(leq(height(r), Nat::S(height(lr))));
                            instantiate!(eq_nat(
                                Nat::S(max(height(lr), height(r))),
                                Nat::S(max(height(lr), height(r)))
                            ));
                            instantiate!(leq(height(_lrl), Nat::S(height(_lrr))));
                            instantiate!(leq(height(_lrr), Nat::S(height(_lrl))));
                            instantiate!(eq_nat(_lrh, Nat::S(max(height(_lrl), height(_lrr)))));
                            instantiate!(is_balanced(_lrl));
                            instantiate!(is_balanced(_lrr));
                            instantiate!(eq_nat(
                                max(height(lr), height(r)),
                                max(height(lr), height(r))
                            ));
                            leq_contra(height(r.clone()), height(l.clone()));
                            leq_succ_l(height(r.clone()), height(l.clone()));
                            max_leq(height(l.clone()), height(r.clone()));
                            eq_nat_eq(
                                h.clone(),
                                Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                            );
                            eq_nat_eq(
                                _lh.clone(),
                                Nat::S(Box::new(max(height(*_ll.clone()), height(*lr.clone())))),
                            );
                            max_leq(height(*_ll.clone()), height(*lr.clone()));
                            leq_succ_l(height(r.clone()), height(*_ll.clone()));
                            leq_trans(
                                Nat::S(Box::new(height(r.clone()))),
                                height(*_ll.clone()),
                                Nat::S(Box::new(height(*lr.clone()))),
                            );
                            max_leq(height(*lr.clone()), height(r.clone()));
                            leq_succ_r(height(*_ll.clone()), Nat::S(Box::new(height(*lr.clone()))));
                            eq_nat_refl(max(
                                height(*_ll.clone()),
                                height(node(*lr.clone(), v.clone(), r.clone())),
                            ));
                            leq_succ_r(height(l2.clone()), Nat::S(Box::new(height(r.clone()))));
                            leq_trans(
                                height(*lr.clone()),
                                height(*_ll.clone()),
                                Nat::S(Box::new(height(r.clone()))),
                            );
                            leq_succ_r(height(r.clone()), height(*lr.clone()));
                            eq_nat_refl(max(height(*lr.clone()), height(r.clone())));
                            max_leq_r(height(*_ll.clone()), Nat::S(Box::new(height(*lr.clone()))));
                            leq_antisym_succ(height(*_ll.clone()), height(*lr.clone()));
                        } else {
                            // double rotation
                            instantiate!(node(node(_ll, _lv, _lrl), _lrv, node(_lrr, v, r)));
                            instantiate!(leq(height(_lrl), Nat::S(height(_lrr))));
                            instantiate!(leq(height(_lrr), Nat::S(height(_lrl))));
                            instantiate!(eq_nat(_lrh, Nat::S(max(height(_lrl), height(_lrr)))));
                            instantiate!(is_balanced(_lrl));
                            instantiate!(is_balanced(_lrr));
                            instantiate!(Tree::Node(
                                node(_ll, _lv, _lrl),
                                _lrv,
                                Nat::S(max(height(node(_ll, _lv, _lrl)), height(node(_lrr, v, r)))),
                                node(_lrr, v, r)
                            ));
                            instantiate!(Tree::Node(
                                _ll,
                                _lv,
                                Nat::S(max(height(_ll), height(_lrl))),
                                _lrl
                            ));
                            instantiate!(Tree::Node(
                                _lrr,
                                v,
                                Nat::S(max(height(_lrr), height(r))),
                                r
                            ));
                            instantiate!(leq(
                                height(node(_ll, _lv, _lrl)),
                                Nat::S(height(node(_lrr, v, r)))
                            ));
                            instantiate!(leq(
                                height(node(_lrr, v, r)),
                                Nat::S(height(node(_ll, _lv, _lrl)))
                            ));
                            instantiate!(eq_nat(
                                Nat::S(max(height(node(_ll, _lv, _lrl)), height(node(_lrr, v, r)))),
                                Nat::S(max(height(node(_ll, _lv, _lrl)), height(node(_lrr, v, r))))
                            ));
                            instantiate!(is_balanced(node(_ll, _lv, _lrl)));
                            instantiate!(is_balanced(node(_lrr, v, r)));
                            instantiate!(Nat::S(max(
                                max(height(_ll), height(_lrl)),
                                max(height(_lrr), height(r))
                            )));
                            instantiate!(leq(
                                max(height(_ll), height(_lrl)),
                                height(node(_lrr, v, r))
                            ));
                            instantiate!(leq(
                                max(height(_lrr), height(r)),
                                height(node(_ll, _lv, _lrl))
                            ));
                            instantiate!(eq_nat(
                                max(height(node(_ll, _lv, _lrl)), height(node(_lrr, v, r))),
                                max(height(node(_ll, _lv, _lrl)), height(node(_lrr, v, r)))
                            ));
                            instantiate!(leq(height(_ll), Nat::S(height(_lrl))));
                            instantiate!(leq(height(_lrl), Nat::S(height(_ll))));
                            instantiate!(eq_nat(
                                Nat::S(max(height(_ll), height(_lrl))),
                                Nat::S(max(height(_ll), height(_lrl)))
                            ));
                            instantiate!(leq(height(_lrr), Nat::S(height(r))));
                            instantiate!(leq(height(r), Nat::S(height(_lrr))));
                            instantiate!(eq_nat(
                                Nat::S(max(height(_lrr), height(r))),
                                Nat::S(max(height(_lrr), height(r)))
                            ));
                            instantiate!(eq_nat(
                                max(max(height(_ll), height(_lrl)), max(height(_lrr), height(r))),
                                max(max(height(_ll), height(_lrl)), max(height(_lrr), height(r)))
                            ));
                            instantiate!(eq_nat(
                                max(height(_ll), height(_lrl)),
                                max(height(_ll), height(_lrl))
                            ));
                            instantiate!(eq_nat(
                                max(height(_lrr), height(r)),
                                max(height(_lrr), height(r))
                            ));
                            leq_contra(height(r.clone()), height(l.clone()));
                            leq_succ_l(height(r.clone()), height(l.clone()));
                            max_leq(height(l.clone()), height(r.clone()));
                            eq_nat_eq(
                                h.clone(),
                                Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                            );
                            eq_nat_eq(
                                _lh.clone(),
                                Nat::S(Box::new(max(height(*_ll.clone()), height(*lr.clone())))),
                            );
                            leq_neg_lt(height(*lr.clone()), height(*_ll.clone()));
                            leq_succ_l(height(*_ll.clone()), height(*lr.clone()));
                            max_leq_r(height(*_ll.clone()), height(*lr.clone()));
                            leq_succ_r(height(l2.clone()), Nat::S(Box::new(height(r.clone()))));
                            leq_antisym(height(*lr.clone()), Nat::S(Box::new(height(r.clone()))));
                            eq_nat_eq(
                                _lrh.clone(),
                                Nat::S(Box::new(max(height(*_lrl.clone()), height(*_lrr.clone())))),
                            );
                            leq_max_l(height(*_lrl.clone()), height(*_lrr.clone()));
                            leq_max_r(height(*_lrl.clone()), height(*_lrr.clone()));
                            leq_trans(
                                height(*_lrl.clone()),
                                max(height(*_lrl.clone()), height(*_lrr.clone())),
                                height(*_ll.clone()),
                            );
                            leq_trans(
                                height(*_lrr.clone()),
                                max(height(*_lrl.clone()), height(*_lrr.clone())),
                                height(r.clone()),
                            );
                            leq_trans(
                                height(r.clone()),
                                max(height(*_lrl.clone()), height(*_lrr.clone())),
                                height(*_ll.clone()),
                            );
                            leq_trans(
                                height(*_ll.clone()),
                                max(height(*_lrl.clone()), height(*_lrr.clone())),
                                height(r.clone()),
                            );
                            leq_succ_self(height(*_lrl.clone()));
                            max_bound(
                                height(*_lrl.clone()),
                                height(*_lrr.clone()),
                                Nat::S(Box::new(height(*_lrl.clone()))),
                            );
                            leq_trans(
                                height(*_ll.clone()),
                                max(height(*_lrl.clone()), height(*_lrr.clone())),
                                Nat::S(Box::new(height(*_lrl.clone()))),
                            );
                            leq_succ_r(height(*_lrl.clone()), height(*_ll.clone()));
                            eq_nat_refl(max(height(*_ll.clone()), height(*_lrl.clone())));
                            leq_succ_r(height(*_lrr.clone()), height(r.clone()));
                            leq_succ_self(height(*_lrr.clone()));
                            max_bound(
                                height(*_lrl.clone()),
                                height(*_lrr.clone()),
                                Nat::S(Box::new(height(*_lrr.clone()))),
                            );
                            leq_trans(
                                height(r.clone()),
                                max(height(*_lrl.clone()), height(*_lrr.clone())),
                                Nat::S(Box::new(height(*_lrr.clone()))),
                            );
                            eq_nat_refl(max(height(*_lrr.clone()), height(r.clone())));
                            max_leq(height(*_ll.clone()), height(*_lrl.clone()));
                            max_leq_r(height(*_lrr.clone()), height(r.clone()));
                            leq_succ_r(height(*_ll.clone()), height(r.clone()));
                            leq_succ_r(height(r.clone()), height(*_ll.clone()));
                            eq_nat_refl(max(
                                max(height(*_ll.clone()), height(*_lrl.clone())),
                                max(height(*_lrr.clone()), height(r.clone())),
                            ));
                            max_leq(height(*_ll.clone()), height(r.clone()));
                            leq_antisym(
                                height(*lr.clone()),
                                Nat::S(Box::new(height(*_ll.clone()))),
                            );
                        }
                    } else {
                        if leq(
                            Nat::S(Box::new(Nat::S(Box::new(height(l2.clone()))))),
                            height(r.clone()),
                        ) {
                            // G2 (rotate left: impossible)
                            instantiate!(leq(height(r), Nat::S(height(l2))));
                            leq_succ_r(height(r.clone()), Nat::S(Box::new(height(l.clone()))));
                            leq_contra(height(l2.clone()), height(r.clone()));
                        } else {
                            // else (node)
                            instantiate!(Tree::Node(l2, v, Nat::S(max(height(l2), height(r))), r));
                            instantiate!(leq(height(l2), Nat::S(height(r))));
                            instantiate!(leq(height(r), Nat::S(height(l2))));
                            instantiate!(eq_nat(
                                Nat::S(max(height(l2), height(r))),
                                Nat::S(max(height(l2), height(r)))
                            ));
                            instantiate!(eq_nat(
                                max(height(l2), height(r)),
                                max(height(l2), height(r))
                            ));
                            leq_neg_strong(Nat::S(Box::new(height(r.clone()))), height(l2.clone()));
                            leq_neg_strong(Nat::S(Box::new(height(l2.clone()))), height(r.clone()));
                            eq_nat_refl(max(height(l2.clone()), height(r.clone())));
                            max_succ_l(height(l.clone()), height(r.clone()));
                            eq_nat_eq(
                                h.clone(),
                                Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                            );
                        }
                    }
                }
            },
        }
    }

    // Helper: max(x, S(y)) is max(x, y) or S(max(x, y)).
    #[val((x: Nat, y: Nat) -> Lemma(max(x, Nat::S(Box::new(y))) == max(x, y)
        || max(x, Nat::S(Box::new(y))) == Nat::S(Box::new(max(x, y)))))]
    fn max_succ_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => match y {
                Nat::Z => {
                    instantiate!(Nat::S(max(x_min, y)));
                    max_zero_r(*x_min.clone());
                }
                Nat::S(y_min) => {
                    max_succ_r(*x_min, *y_min);
                }
            },
        }
    }

    // Helper: rebalancing after the right subtree grew by at most one keeps
    // the tree balanced, with height h or S(h). Mirror of bal_left.
    #[val((l: Tree, v: Nat, h: Nat, r: Tree, r2: Tree) -> Lemma(implies(
        is_balanced(Tree::Node(Box::new(l), v, h, Box::new(r)))
            && is_balanced(r2)
            && (height(r2) == height(r) || height(r2) == Nat::S(Box::new(height(r)))),
        is_balanced(balance(l, v, r2))
            && (height(balance(l, v, r2)) == h
                || height(balance(l, v, r2)) == Nat::S(Box::new(h))))))]
    fn bal_right(l: Tree, v: Nat, h: Nat, r: Tree, r2: Tree) {
        match r2.clone() {
            Tree::Leaf => {
                instantiate!(leq(height(l), Nat::S(height(r))));
                instantiate!(leq(height(r), Nat::S(height(l))));
                instantiate!(eq_nat(h, Nat::S(max(height(l), height(r)))));
                instantiate!(is_balanced(l));
                instantiate!(is_balanced(r));
                instantiate!(leq(Nat::S(Nat::S(height(r2))), height(l)));
                instantiate!(rotate_right(l, v, r2));
                instantiate!(leq(Nat::S(Nat::S(height(l))), height(r2)));
                instantiate!(rotate_left(l, v, r2));
                instantiate!(node(l, v, r2));
                instantiate!(Tree::Node(l, v, Nat::S(max(height(l), height(r2))), r2));
                instantiate!(leq(height(l), Nat::S(height(r2))));
                instantiate!(leq(height(r2), Nat::S(height(l))));
                instantiate!(eq_nat(
                    Nat::S(max(height(l), height(r2))),
                    Nat::S(max(height(l), height(r2)))
                ));
                instantiate!(eq_nat(
                    max(height(l), height(r2)),
                    max(height(l), height(r2))
                ));
                eq_nat_refl(max(height(l.clone()), height(r2.clone())));
                leq_contra(height(r2.clone()), height(l.clone()));
                eq_nat_eq(
                    h.clone(),
                    Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                );
            }
            Tree::Node(rl, _rv, _rh, _rr) => match *rl.clone() {
                Tree::Leaf => {
                    instantiate!(leq(height(l), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l))));
                    instantiate!(eq_nat(h, Nat::S(max(height(l), height(r)))));
                    instantiate!(is_balanced(l));
                    instantiate!(is_balanced(r));
                    instantiate!(leq(height(rl), Nat::S(height(_rr))));
                    instantiate!(leq(height(_rr), Nat::S(height(rl))));
                    instantiate!(eq_nat(_rh, Nat::S(max(height(rl), height(_rr)))));
                    instantiate!(is_balanced(rl));
                    instantiate!(is_balanced(_rr));
                    instantiate!(leq(Nat::S(Nat::S(height(r2))), height(l)));
                    instantiate!(rotate_right(l, v, r2));
                    instantiate!(leq(Nat::S(Nat::S(height(l))), height(r2)));
                    instantiate!(rotate_left(l, v, r2));
                    instantiate!(node(l, v, r2));
                    instantiate!(leq(height(rl), height(_rr)));
                    instantiate!(node(node(l, v, rl), _rv, _rr));
                    instantiate!(Tree::Node(l, v, Nat::S(max(height(l), height(r2))), r2));
                    instantiate!(Tree::Node(
                        node(l, v, rl),
                        _rv,
                        Nat::S(max(height(node(l, v, rl)), height(_rr))),
                        _rr
                    ));
                    instantiate!(Tree::Node(l, v, Nat::S(max(height(l), height(rl))), rl));
                    instantiate!(leq(height(l), Nat::S(height(r2))));
                    instantiate!(leq(height(r2), Nat::S(height(l))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(l), height(r2))),
                        Nat::S(max(height(l), height(r2)))
                    ));
                    instantiate!(leq(height(node(l, v, rl)), Nat::S(height(_rr))));
                    instantiate!(leq(height(_rr), Nat::S(height(node(l, v, rl)))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(node(l, v, rl)), height(_rr))),
                        Nat::S(max(height(node(l, v, rl)), height(_rr)))
                    ));
                    instantiate!(is_balanced(node(l, v, rl)));
                    instantiate!(eq_nat(
                        max(height(l), height(r2)),
                        max(height(l), height(r2))
                    ));
                    instantiate!(leq(max(height(l), height(rl)), height(_rr)));
                    instantiate!(eq_nat(
                        max(height(node(l, v, rl)), height(_rr)),
                        max(height(node(l, v, rl)), height(_rr))
                    ));
                    instantiate!(leq(height(l), Nat::S(height(rl))));
                    instantiate!(leq(height(rl), Nat::S(height(l))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(l), height(rl))),
                        Nat::S(max(height(l), height(rl)))
                    ));
                    instantiate!(eq_nat(
                        max(height(l), height(rl)),
                        max(height(l), height(rl))
                    ));
                    // G2 (rotate left)
                    eq_nat_eq(
                        _rh.clone(),
                        Nat::S(Box::new(max(height(*rl.clone()), height(*_rr.clone())))),
                    );
                    max_zero_r(height(l.clone()));
                    leq_succ_l(height(l.clone()), height(*_rr.clone()));
                    leq_trans(
                        height(*_rr.clone()),
                        Nat::S(Box::new(height(*rl.clone()))),
                        Nat::S(Box::new(height(node(l.clone(), v.clone(), *rl.clone())))),
                    );
                    leq_trans(
                        height(l.clone()),
                        height(*_rr.clone()),
                        Nat::S(Box::new(height(*rl.clone()))),
                    );
                    eq_nat_refl(max(
                        height(node(l.clone(), v.clone(), *rl.clone())),
                        height(*_rr.clone()),
                    ));
                    eq_nat_refl(max(height(l.clone()), height(*rl.clone())));
                    max_leq_r(
                        height(node(l.clone(), v.clone(), *rl.clone())),
                        height(*_rr.clone()),
                    );
                    leq_contra(height(l.clone()), height(r.clone()));
                    max_leq_r(height(l.clone()), height(r.clone()));
                    leq_succ_l(height(l.clone()), height(r.clone()));
                    eq_nat_eq(
                        h.clone(),
                        Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                    );
                    // G1 (rotate right: impossible)
                    leq_succ_r(height(l.clone()), Nat::S(Box::new(height(r.clone()))));
                    leq_contra(height(r2.clone()), height(l.clone()));
                    // else (node)
                    leq_neg_strong(Nat::S(Box::new(height(r2.clone()))), height(l.clone()));
                    leq_neg_strong(Nat::S(Box::new(height(l.clone()))), height(r2.clone()));
                    eq_nat_refl(max(height(l.clone()), height(r2.clone())));
                    max_succ_r(height(l.clone()), height(r.clone()));
                }
                Tree::Node(_rll, _rlv, _rlh, _rlr) => {
                    instantiate!(leq(height(l), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l))));
                    instantiate!(eq_nat(h, Nat::S(max(height(l), height(r)))));
                    instantiate!(is_balanced(l));
                    instantiate!(is_balanced(r));
                    instantiate!(leq(height(rl), Nat::S(height(_rr))));
                    instantiate!(leq(height(_rr), Nat::S(height(rl))));
                    instantiate!(eq_nat(_rh, Nat::S(max(height(rl), height(_rr)))));
                    instantiate!(is_balanced(rl));
                    instantiate!(is_balanced(_rr));
                    instantiate!(leq(Nat::S(Nat::S(height(r2))), height(l)));
                    instantiate!(rotate_right(l, v, r2));
                    instantiate!(leq(Nat::S(Nat::S(height(l))), height(r2)));
                    instantiate!(rotate_left(l, v, r2));
                    instantiate!(node(l, v, r2));
                    if leq(
                        Nat::S(Box::new(Nat::S(Box::new(height(r2.clone()))))),
                        height(l.clone()),
                    ) {
                        // G1 (rotate right: impossible)
                        instantiate!(leq(height(l), Nat::S(height(r2))));
                        leq_succ_r(height(l.clone()), Nat::S(Box::new(height(r.clone()))));
                        leq_contra(height(r2.clone()), height(l.clone()));
                    } else {
                        if leq(
                            Nat::S(Box::new(Nat::S(Box::new(height(l.clone()))))),
                            height(r2.clone()),
                        ) {
                            // G2 (rotate left)
                            instantiate!(leq(height(rl), height(_rr)));
                            if leq(height(*rl.clone()), height(*_rr.clone())) {
                                // single rotation
                                instantiate!(node(node(l, v, rl), _rv, _rr));
                                instantiate!(Tree::Node(
                                    node(l, v, rl),
                                    _rv,
                                    Nat::S(max(height(node(l, v, rl)), height(_rr))),
                                    _rr
                                ));
                                instantiate!(Tree::Node(
                                    l,
                                    v,
                                    Nat::S(max(height(l), height(rl))),
                                    rl
                                ));
                                instantiate!(leq(height(node(l, v, rl)), Nat::S(height(_rr))));
                                instantiate!(leq(height(_rr), Nat::S(height(node(l, v, rl)))));
                                instantiate!(eq_nat(
                                    Nat::S(max(height(node(l, v, rl)), height(_rr))),
                                    Nat::S(max(height(node(l, v, rl)), height(_rr)))
                                ));
                                instantiate!(is_balanced(node(l, v, rl)));
                                instantiate!(leq(max(height(l), height(rl)), height(_rr)));
                                instantiate!(eq_nat(
                                    max(height(node(l, v, rl)), height(_rr)),
                                    max(height(node(l, v, rl)), height(_rr))
                                ));
                                instantiate!(leq(height(l), Nat::S(height(rl))));
                                instantiate!(leq(height(rl), Nat::S(height(l))));
                                instantiate!(eq_nat(
                                    Nat::S(max(height(l), height(rl))),
                                    Nat::S(max(height(l), height(rl)))
                                ));
                                instantiate!(leq(height(_rll), Nat::S(height(_rlr))));
                                instantiate!(leq(height(_rlr), Nat::S(height(_rll))));
                                instantiate!(eq_nat(_rlh, Nat::S(max(height(_rll), height(_rlr)))));
                                instantiate!(is_balanced(_rll));
                                instantiate!(is_balanced(_rlr));
                                instantiate!(eq_nat(
                                    max(height(l), height(rl)),
                                    max(height(l), height(rl))
                                ));
                                leq_contra(height(l.clone()), height(r.clone()));
                                leq_succ_l(height(l.clone()), height(r.clone()));
                                max_leq_r(height(l.clone()), height(r.clone()));
                                eq_nat_eq(
                                    h.clone(),
                                    Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                                );
                                eq_nat_eq(
                                    _rh.clone(),
                                    Nat::S(Box::new(max(
                                        height(*rl.clone()),
                                        height(*_rr.clone()),
                                    ))),
                                );
                                max_leq_r(height(*rl.clone()), height(*_rr.clone()));
                                leq_succ_l(height(l.clone()), height(*_rr.clone()));
                                leq_trans(
                                    Nat::S(Box::new(height(l.clone()))),
                                    height(*_rr.clone()),
                                    Nat::S(Box::new(height(*rl.clone()))),
                                );
                                max_leq_r(height(l.clone()), height(*rl.clone()));
                                leq_succ_r(
                                    height(*_rr.clone()),
                                    Nat::S(Box::new(height(*rl.clone()))),
                                );
                                eq_nat_refl(max(
                                    height(node(l.clone(), v.clone(), *rl.clone())),
                                    height(*_rr.clone()),
                                ));
                                leq_succ_r(height(r2.clone()), Nat::S(Box::new(height(l.clone()))));
                                leq_trans(
                                    height(*rl.clone()),
                                    height(*_rr.clone()),
                                    Nat::S(Box::new(height(l.clone()))),
                                );
                                leq_succ_r(height(l.clone()), height(*rl.clone()));
                                eq_nat_refl(max(height(l.clone()), height(*rl.clone())));
                                max_leq(
                                    Nat::S(Box::new(height(*rl.clone()))),
                                    height(*_rr.clone()),
                                );
                                leq_antisym_succ(height(*_rr.clone()), height(*rl.clone()));
                            } else {
                                // double rotation
                                instantiate!(node(node(l, v, _rll), _rlv, node(_rlr, _rv, _rr)));
                                instantiate!(leq(height(_rll), Nat::S(height(_rlr))));
                                instantiate!(leq(height(_rlr), Nat::S(height(_rll))));
                                instantiate!(eq_nat(_rlh, Nat::S(max(height(_rll), height(_rlr)))));
                                instantiate!(is_balanced(_rll));
                                instantiate!(is_balanced(_rlr));
                                instantiate!(Tree::Node(
                                    node(l, v, _rll),
                                    _rlv,
                                    Nat::S(max(
                                        height(node(l, v, _rll)),
                                        height(node(_rlr, _rv, _rr))
                                    )),
                                    node(_rlr, _rv, _rr)
                                ));
                                instantiate!(Tree::Node(
                                    l,
                                    v,
                                    Nat::S(max(height(l), height(_rll))),
                                    _rll
                                ));
                                instantiate!(Tree::Node(
                                    _rlr,
                                    _rv,
                                    Nat::S(max(height(_rlr), height(_rr))),
                                    _rr
                                ));
                                instantiate!(leq(
                                    height(node(l, v, _rll)),
                                    Nat::S(height(node(_rlr, _rv, _rr)))
                                ));
                                instantiate!(leq(
                                    height(node(_rlr, _rv, _rr)),
                                    Nat::S(height(node(l, v, _rll)))
                                ));
                                instantiate!(eq_nat(
                                    Nat::S(max(
                                        height(node(l, v, _rll)),
                                        height(node(_rlr, _rv, _rr))
                                    )),
                                    Nat::S(max(
                                        height(node(l, v, _rll)),
                                        height(node(_rlr, _rv, _rr))
                                    ))
                                ));
                                instantiate!(is_balanced(node(l, v, _rll)));
                                instantiate!(is_balanced(node(_rlr, _rv, _rr)));
                                instantiate!(Nat::S(max(
                                    max(height(l), height(_rll)),
                                    max(height(_rlr), height(_rr))
                                )));
                                instantiate!(leq(
                                    max(height(l), height(_rll)),
                                    height(node(_rlr, _rv, _rr))
                                ));
                                instantiate!(leq(
                                    max(height(_rlr), height(_rr)),
                                    height(node(l, v, _rll))
                                ));
                                instantiate!(eq_nat(
                                    max(height(node(l, v, _rll)), height(node(_rlr, _rv, _rr))),
                                    max(height(node(l, v, _rll)), height(node(_rlr, _rv, _rr)))
                                ));
                                instantiate!(leq(height(l), Nat::S(height(_rll))));
                                instantiate!(leq(height(_rll), Nat::S(height(l))));
                                instantiate!(eq_nat(
                                    Nat::S(max(height(l), height(_rll))),
                                    Nat::S(max(height(l), height(_rll)))
                                ));
                                instantiate!(leq(height(_rlr), Nat::S(height(_rr))));
                                instantiate!(leq(height(_rr), Nat::S(height(_rlr))));
                                instantiate!(eq_nat(
                                    Nat::S(max(height(_rlr), height(_rr))),
                                    Nat::S(max(height(_rlr), height(_rr)))
                                ));
                                instantiate!(eq_nat(
                                    max(
                                        max(height(l), height(_rll)),
                                        max(height(_rlr), height(_rr))
                                    ),
                                    max(
                                        max(height(l), height(_rll)),
                                        max(height(_rlr), height(_rr))
                                    )
                                ));
                                instantiate!(eq_nat(
                                    max(height(l), height(_rll)),
                                    max(height(l), height(_rll))
                                ));
                                instantiate!(eq_nat(
                                    max(height(_rlr), height(_rr)),
                                    max(height(_rlr), height(_rr))
                                ));
                                leq_contra(height(l.clone()), height(r.clone()));
                                leq_succ_l(height(l.clone()), height(r.clone()));
                                max_leq_r(height(l.clone()), height(r.clone()));
                                eq_nat_eq(
                                    h.clone(),
                                    Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                                );
                                eq_nat_eq(
                                    _rh.clone(),
                                    Nat::S(Box::new(max(
                                        height(*rl.clone()),
                                        height(*_rr.clone()),
                                    ))),
                                );
                                leq_neg_lt(height(*rl.clone()), height(*_rr.clone()));
                                leq_succ_l(height(*_rr.clone()), height(*rl.clone()));
                                max_leq(height(*rl.clone()), height(*_rr.clone()));
                                leq_succ_r(height(r2.clone()), Nat::S(Box::new(height(l.clone()))));
                                leq_antisym(
                                    height(*rl.clone()),
                                    Nat::S(Box::new(height(l.clone()))),
                                );
                                eq_nat_eq(
                                    _rlh.clone(),
                                    Nat::S(Box::new(max(
                                        height(*_rll.clone()),
                                        height(*_rlr.clone()),
                                    ))),
                                );
                                leq_max_l(height(*_rll.clone()), height(*_rlr.clone()));
                                leq_max_r(height(*_rll.clone()), height(*_rlr.clone()));
                                leq_trans(
                                    height(*_rlr.clone()),
                                    max(height(*_rll.clone()), height(*_rlr.clone())),
                                    height(*_rr.clone()),
                                );
                                leq_trans(
                                    height(*_rll.clone()),
                                    max(height(*_rll.clone()), height(*_rlr.clone())),
                                    height(l.clone()),
                                );
                                leq_trans(
                                    height(l.clone()),
                                    max(height(*_rll.clone()), height(*_rlr.clone())),
                                    height(*_rr.clone()),
                                );
                                leq_trans(
                                    height(*_rr.clone()),
                                    max(height(*_rll.clone()), height(*_rlr.clone())),
                                    height(l.clone()),
                                );
                                leq_succ_self(height(*_rlr.clone()));
                                max_bound(
                                    height(*_rll.clone()),
                                    height(*_rlr.clone()),
                                    Nat::S(Box::new(height(*_rlr.clone()))),
                                );
                                leq_trans(
                                    height(*_rr.clone()),
                                    max(height(*_rll.clone()), height(*_rlr.clone())),
                                    Nat::S(Box::new(height(*_rlr.clone()))),
                                );
                                leq_succ_r(height(*_rlr.clone()), height(*_rr.clone()));
                                eq_nat_refl(max(height(*_rlr.clone()), height(*_rr.clone())));
                                leq_succ_self(height(*_rll.clone()));
                                max_bound(
                                    height(*_rll.clone()),
                                    height(*_rlr.clone()),
                                    Nat::S(Box::new(height(*_rll.clone()))),
                                );
                                leq_trans(
                                    height(l.clone()),
                                    max(height(*_rll.clone()), height(*_rlr.clone())),
                                    Nat::S(Box::new(height(*_rll.clone()))),
                                );
                                leq_succ_r(height(*_rll.clone()), height(l.clone()));
                                eq_nat_refl(max(height(l.clone()), height(*_rll.clone())));
                                max_leq(height(l.clone()), height(*_rll.clone()));
                                max_leq_r(height(*_rlr.clone()), height(*_rr.clone()));
                                leq_succ_r(height(l.clone()), height(*_rr.clone()));
                                leq_succ_r(height(*_rr.clone()), height(l.clone()));
                                eq_nat_refl(max(
                                    max(height(l.clone()), height(*_rll.clone())),
                                    max(height(*_rlr.clone()), height(*_rr.clone())),
                                ));
                                max_leq_r(height(l.clone()), height(*_rr.clone()));
                                leq_antisym(
                                    height(*rl.clone()),
                                    Nat::S(Box::new(height(*_rr.clone()))),
                                );
                            }
                        } else {
                            // else (node)
                            instantiate!(Tree::Node(l, v, Nat::S(max(height(l), height(r2))), r2));
                            instantiate!(leq(height(l), Nat::S(height(r2))));
                            instantiate!(leq(height(r2), Nat::S(height(l))));
                            instantiate!(eq_nat(
                                Nat::S(max(height(l), height(r2))),
                                Nat::S(max(height(l), height(r2)))
                            ));
                            instantiate!(eq_nat(
                                max(height(l), height(r2)),
                                max(height(l), height(r2))
                            ));
                            leq_neg_strong(Nat::S(Box::new(height(r2.clone()))), height(l.clone()));
                            leq_neg_strong(Nat::S(Box::new(height(l.clone()))), height(r2.clone()));
                            eq_nat_refl(max(height(l.clone()), height(r2.clone())));
                            max_succ_r(height(l.clone()), height(r.clone()));
                            eq_nat_eq(
                                h.clone(),
                                Nat::S(Box::new(max(height(l.clone()), height(r.clone())))),
                            );
                        }
                    }
                }
            },
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
        match t.clone() {
            Tree::Leaf => {
                instantiate!(Tree::Node(Tree::Leaf, x, Nat::S(Nat::Z), Tree::Leaf));
                instantiate!(leq(height(Tree::Leaf), Nat::S(height(Tree::Leaf))));
                instantiate!(eq_nat(
                    Nat::S(Nat::Z),
                    Nat::S(max(height(Tree::Leaf), height(Tree::Leaf)))
                ));
                instantiate!(is_balanced(Tree::Leaf));
                instantiate!(eq_nat(Nat::Z, max(height(Tree::Leaf), height(Tree::Leaf))));
            }
            Tree::Node(l, v, _, r) => {
                if lt(x.clone(), v.clone()) {
                    instantiate!(balance(insert(x, l), v, r));
                    instantiate!(lt(v, x));
                    instantiate!(leq(height(l), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l))));
                    instantiate!(eq_nat(height(t), Nat::S(max(height(l), height(r)))));
                    instantiate!(is_balanced(l));
                    instantiate!(is_balanced(r));
                    instantiate!(leq(Nat::S(Nat::S(height(r))), height(insert(x, l))));
                    instantiate!(rotate_right(insert(x, l), v, r));
                    instantiate!(leq(Nat::S(Nat::S(height(insert(x, l)))), height(r)));
                    instantiate!(rotate_left(insert(x, l), v, r));
                    instantiate!(node(insert(x, l), v, r));
                    instantiate!(Tree::Node(
                        insert(x, l),
                        v,
                        Nat::S(max(height(insert(x, l)), height(r))),
                        r
                    ));
                    instantiate!(leq(height(insert(x, l)), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(insert(x, l)))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(insert(x, l)), height(r))),
                        Nat::S(max(height(insert(x, l)), height(r)))
                    ));
                    instantiate!(eq_nat(
                        max(height(insert(x, l)), height(r)),
                        max(height(insert(x, l)), height(r))
                    ));
                    instantiate!(leq(Nat::S(height(r)), height(l)));
                    instantiate!(leq(height(l), height(r)));
                    insert_correct(x.clone(), *r.clone());
                    bal_left(
                        *l.clone(),
                        v.clone(),
                        height(t.clone()),
                        *r.clone(),
                        insert(x.clone(), *l.clone()),
                    );
                    insert_correct(x, *l);
                } else if lt(v.clone(), x.clone()) {
                    instantiate!(balance(l, v, insert(x, r)));
                    instantiate!(leq(height(l), Nat::S(height(r))));
                    instantiate!(leq(height(r), Nat::S(height(l))));
                    instantiate!(eq_nat(height(t), Nat::S(max(height(l), height(r)))));
                    instantiate!(is_balanced(l));
                    instantiate!(is_balanced(r));
                    instantiate!(leq(Nat::S(Nat::S(height(insert(x, r)))), height(l)));
                    instantiate!(rotate_right(l, v, insert(x, r)));
                    instantiate!(leq(Nat::S(Nat::S(height(l))), height(insert(x, r))));
                    instantiate!(rotate_left(l, v, insert(x, r)));
                    instantiate!(node(l, v, insert(x, r)));
                    instantiate!(Tree::Node(
                        l,
                        v,
                        Nat::S(max(height(l), height(insert(x, r)))),
                        insert(x, r)
                    ));
                    instantiate!(leq(height(l), Nat::S(height(insert(x, r)))));
                    instantiate!(leq(height(insert(x, r)), Nat::S(height(l))));
                    instantiate!(eq_nat(
                        Nat::S(max(height(l), height(insert(x, r)))),
                        Nat::S(max(height(l), height(insert(x, r))))
                    ));
                    instantiate!(eq_nat(
                        max(height(l), height(insert(x, r))),
                        max(height(l), height(insert(x, r)))
                    ));
                    instantiate!(leq(Nat::S(height(l)), height(r)));
                    instantiate!(leq(height(r), height(l)));
                    bal_right(
                        *l.clone(),
                        v.clone(),
                        height(t.clone()),
                        *r.clone(),
                        insert(x.clone(), *r.clone()),
                    );
                    insert_correct(x, *r);
                } else {
                    ()
                }
            }
        }
    }
}
