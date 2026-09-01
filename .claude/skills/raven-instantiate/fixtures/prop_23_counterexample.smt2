; ravencheck counterexample
; lemma  : tip_23   [vc 6]
; goal   : max(a, b) == max(b, a)
; branch : a = S(a_min), b = S(b_min)
;
; definitions:
;   max(Z, y)               = y
;   max(S(x_min), Z)        = S(x_min)
;   max(S(x_min), S(y_min)) = S(max(x_min, y_min))

(declare-sort Nat 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-fun max (Nat Nat) Nat)

(declare-const b Nat)
(declare-const a Nat)
(declare-const a_min Nat)
(declare-const b_min Nat)

(assert (= a (S a_min)))
(assert (= b (S b_min)))

; instantiated terms:
;   from the goal:
;     (max a b)   (max b a)
;   from the hypothesis (max a_min b_min) == (max b_min a_min):
;     (max a_min b_min)   (max b_min a_min)
;   from patterns:
;     (S a_min)   (S b_min)

(assert (distinct (max a b) (max b a)))
(check-sat)
