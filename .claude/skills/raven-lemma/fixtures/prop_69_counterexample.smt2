; ravencheck counterexample
; lemma  : tip_69   [vc 4]
; goal   : le(n, add(m, n))
; branch : n = S(n_min)
;
; definitions:
;   add(Z, y)              = y
;   add(S(x_min), y)       = S(add(x_min, y))
;   le(Z, y)               = true
;   le(S(x_min), Z)        = false
;   le(S(x_min), S(y_min)) = le(x_min, y_min)

(declare-sort Nat 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-fun add (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)

(declare-const m Nat)
(declare-const n Nat)
(declare-const n_min Nat)

(assert (= n (S n_min)))

; instantiated terms:
;   from the goal:
;     (add m n)   (le n (add m n))
;   from the hypothesis (le n_min (add m n_min)):
;     (add m n_min)   (le n_min (add m n_min))
;   from patterns:
;     (S n_min)

(assert (= (le n (add m n)) false))
(check-sat)
