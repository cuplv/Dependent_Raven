; ravencheck counterexample
; lemma  : tip_nine   [vc 6]
; goal   : sub(sub(i, j), k) == sub(i, add(j, k))
; branch : i = S(i_prime), j = S(j_prime)
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

(declare-const i Nat)
(declare-const j Nat)
(declare-const k Nat)
(declare-const i_prime Nat)
(declare-const j_prime Nat)

(assert (= i (S i_prime)))
(assert (= j (S j_prime)))

; instantiated terms:
;   from the goal:
;     (sub i j)   (sub (sub i j) k)   (add j k)   (sub i (add j k))
;   from the hypothesis (sub (sub i_prime j_prime) k) == (sub i_prime (add j_prime k)):
;     (sub i_prime j_prime)   (sub (sub i_prime j_prime) k)   (add j_prime k)   (sub i_prime (add j_prime k))
;   from patterns:
;     (S i_prime)   (S j_prime)

(assert (distinct (sub (sub i j) k) (sub i (add j k))))
(check-sat)
