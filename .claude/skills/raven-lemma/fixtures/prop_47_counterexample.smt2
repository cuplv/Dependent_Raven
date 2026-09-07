; ravencheck counterexample
; lemma  : tip_47   [vc 16]
; goal   : height(mirror(t)) == height(t)
; branch : t = Node(l, e, r)
;
; definitions:
;   height(Leaf)            = Z
;   height(Node(l, _e, r))  = S(max(height(l), height(r)))
;   max(Z, y)               = y
;   max(S(x_min), Z)        = S(x_min)
;   max(S(x_min), S(y_min)) = S(max(x_min, y_min))
;   mirror(Leaf)            = Leaf
;   mirror(Node(l, e, r))   = Node(mirror(r), e, mirror(l))

(declare-sort Elem 0)
(declare-sort Nat 0)
(declare-sort Tree 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Leaf Tree)
(declare-fun Node (Tree Elem Tree) Tree)
(declare-fun height (Tree) Nat)
(declare-fun max (Nat Nat) Nat)
(declare-fun mirror (Tree) Tree)

(declare-const t Tree)
(declare-const r Tree)
(declare-const l Tree)
(declare-const e Elem)

(assert (= t (Node l e r)))

; instantiated terms:
;   from the goal:
;     (mirror t)   (height (mirror t))   (height t)
;   from the hypothesis (height (mirror l)) == (height l):
;     (mirror l)   (height (mirror l))   (height l)
;   from the hypothesis (height (mirror r)) == (height r):
;     (mirror r)   (height (mirror r))   (height r)
;   from patterns:
;     (Node l e r)
;   user hints (instantiate!):
;     (Node (mirror r) e (mirror l))   (S (max (height l) (height r)))   (S (max (height (mirror r)) (height (mirror l))))

(assert (distinct (height (mirror t)) (height t)))
(check-sat)
