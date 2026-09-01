; ravencheck counterexample
; lemma  : tip_02   [vc 19]
; goal   : add(count(n, xs), count(n, ys)) == count(n, app(xs, ys))
; branch : xs = Cons(h, t)
;
; definitions:
;   add(Z, y)            = y
;   add(S(x_min), y)     = S(add(x_min, y))
;   app(Nil, y)          = y
;   app(Cons(h, t), y)   = Cons(h, app(t, y))
;   count(x, Nil)        = Z
;   count(x, Cons(h, t)) = if eq_nat(x, h) then S(count(x, t)) else count(x, t)

(declare-sort Nat 0)
(declare-sort NList 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Nil NList)
(declare-fun Cons (Nat NList) NList)
(declare-fun add (Nat Nat) Nat)
(declare-fun app (NList NList) NList)
(declare-fun count (Nat NList) Nat)

(declare-const ys NList)
(declare-const n Nat)
(declare-const xs NList)
(declare-const h Nat)
(declare-const t NList)

(assert (= xs (Cons h t)))

; instantiated terms:
;   from the goal:
;     (count n ys)   (count n xs)   (add (count n xs) (count n ys))   (app xs ys)   (count n (app xs ys))
;   from the hypothesis (add (count n t) (count n ys)) == (count n (app t ys)):
;     (count n t)   (add (count n t) (count n ys))   (app t ys)   (count n (app t ys))
;   from patterns:
;     (Cons h t)
;   user hints (instantiate!):
;     (Cons h (app t ys))   (S (count n (app t ys)))   (S (count n t))   (S (add (count n t) (count n ys)))

(assert (distinct (add (count n xs) (count n ys)) (count n (app xs ys))))
(check-sat)
