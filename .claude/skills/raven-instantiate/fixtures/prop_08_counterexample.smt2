; ravencheck counterexample
; lemma  : tip_eight   [vc 5]
; goal   : sub(add(i, j), add(i, k)) == sub(j, k)
; branch : i = S(i_prime)
;
; definitions:
;   add(Z, y)               = y
;   add(S(x_prime), y)      = S(add(x_prime, y))
;   sub(Z, y)               = Z
;   sub(S(x_min), Z)        = S(x_min)
;   sub(S(x_min), S(y_min)) = sub(x_min, y_min)

(declare-sort Nat 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-fun add (Nat Nat) Nat)
(declare-fun sub (Nat Nat) Nat)

(declare-const k Nat)
(declare-const i Nat)
(declare-const j Nat)
(declare-const i_prime Nat)

(assert (= i (S i_prime)))

; instantiated terms:
;   from the goal:
;     (sub j k)   (add i j)   (add i k)   (sub (add i j) (add i k))
;   from the hypothesis (sub (add i_prime j) (add i_prime k)) == (sub j k):
;     (add i_prime j)   (add i_prime k)   (sub (add i_prime j) (add i_prime k))
;   from patterns:
;     (S i_prime)

(assert (distinct (sub (add i j) (add i k)) (sub j k)))
(check-sat)
