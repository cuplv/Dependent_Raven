; ravencheck counterexample
; lemma  : tip_78   [vc 6]
; goal   : sorted(sort(xs))
; branch : xs = Cons(h, t)
;
; definitions:
;   insort(x, Nil)                = Cons(x, Nil)
;   insort(x, Cons(h, t))         = if le(x, h) then Cons(x, Cons(h, t)) else Cons(h, insort(x, t))
;   sort(Nil)                     = Nil
;   sort(Cons(h, t))              = insort(h, sort(t))
;   sorted(Nil)                   = true
;   sorted(Cons(h, Nil))          = true
;   sorted(Cons(h, Cons(h2, t2))) = if le(h, h2) then sorted(Cons(h2, t2)) else false

(declare-sort Nat 0)
(declare-sort NList 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Nil NList)
(declare-fun Cons (Nat NList) NList)
(declare-fun insort (Nat NList) NList)
(declare-fun sort (NList) NList)
(declare-fun sorted (NList) Bool)

(declare-const xs NList)
(declare-const h Nat)
(declare-const t NList)

(assert (= xs (Cons h t)))

; instantiated terms:
;   from the goal:
;     (sort xs)   (sorted (sort xs))
;   from the hypothesis (sorted (sort t)):
;     (sort t)   (sorted (sort t))
;   from patterns:
;     (Cons h t)
;   user hints (instantiate!):
;     (insort h (sort t))

(assert (= (sorted (sort xs)) false))
(check-sat)
