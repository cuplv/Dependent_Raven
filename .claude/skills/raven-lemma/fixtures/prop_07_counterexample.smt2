; ravencheck counterexample
; lemma  : tip_seven   [vc 1]
; goal   : sub(add(n, m), n) == m
; branch : n = Z
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

(declare-const n Nat)
(declare-const m Nat)

(assert (= n Z))

; instantiated terms:
;   from the goal:
;     (add n m)   (sub (add n m) n)

(assert (distinct (sub (add n m) n) m))
(check-sat)
