; ravencheck counterexample
; lemma  : tip_04   [vc 3]
; goal   : S(count(n, xs)) == count(n, Cons(n, xs))
;
; definitions:
;   count(x, Nil)              = Z
;   count(x, Cons(h, t))       = if eq_nat(x, h) then S(count(x, t)) else count(x, t)
;   eq_nat(Z, Z)               = true
;   eq_nat(Z, S(_y_min))       = false
;   eq_nat(S(x_min), Z)        = false
;   eq_nat(S(x_min), S(y_min)) = eq_nat(x_min, y_min)

(declare-sort Nat 0)
(declare-sort NList 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Nil NList)
(declare-fun Cons (Nat NList) NList)
(declare-fun count (Nat NList) Nat)
(declare-fun eq_nat (Nat Nat) Bool)

(declare-const xs NList)
(declare-const n Nat)

; instantiated terms:
;   from the goal:
;     (count n xs)   (S (count n xs))   (Cons n xs)   (count n (Cons n xs))
;   user hints (instantiate!):
;     (eq_nat n n)

(assert (distinct (S (count n xs)) (count n (Cons n xs))))
(check-sat)
