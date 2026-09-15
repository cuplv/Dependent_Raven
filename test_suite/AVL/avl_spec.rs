// AVL specification, transcribed from ~/Fstar_playground/AVLInductiveSpec.fst.
// Definitions ONLY: no target theorems, no helper lemmas, no hints. This is the
// pristine starting material for proof trials (see README.md); it is never
// edited during a trial.
//
// Section numbers follow the F* file. Transcribes verbatim: `let` before `if`
// (balance) and before a `&&` chain (is_balanced); `&&`/`!` in bodies; `_`
// inside constructor patterns; `else t`; match under if under match
// (rotations). Spelled differently: the two-argument `match x, y with` of
// leq/lt/eq_nat/max become nested single-variable matches with disjoint arms,
// and `Box::new`/`.clone()`/`*` appear so the module compiles as Rust (the
// verifier erases them).
//
// Run directly (registers the definitions, no goals):
//     cargo test -p test_suite --test avl_spec
#[ravencheck::module]
mod avl_spec {

    // (* 1. 순수 귀납적 Nat 데이터 타입 *)
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    // (* 2. 귀납적 대소 비교 및 연산 *)
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

    // (* 3. 트리 데이터 타입 *)  Node(left, value, height, right)
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Tree {
        Leaf,
        Node(Box<Tree>, Nat, Nat, Box<Tree>),
    }

    // (* 4. 높이 조회 및 스마트 생성자 *)
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

    // (* 5. 핵심 불변식 스펙 *)
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

    // (* 6. 회전 연산 *)
    #[val]
    fn rotate_right(l: Tree, v: Nat, r: Tree) -> Tree {
        match l {
            Tree::Node(ll, lv, _, lr) => {
                if leq(height(*lr.clone()), height(*ll.clone())) {
                    node(*ll, lv, node(*lr, v, r))
                } else {
                    match *lr {
                        Tree::Node(lrl, lrv, _, lrr) => node(node(*ll, lv, *lrl), lrv, node(*lrr, v, r)),
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
                        Tree::Node(rll, rlv, _, rlr) => node(node(l, v, *rll), rlv, node(*rlr, rv, *rr)),
                        Tree::Leaf => Tree::Leaf,
                    }
                }
            }
            Tree::Leaf => Tree::Leaf,
        }
    }

    // (* 7. 재균형 함수 *)
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

    // (* 8. AVL 삽입 연산 *)
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
}
