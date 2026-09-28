; ravencheck counterexample
; verdict: sat
; lemma  : tip_64   [vc 3]
; goal   : last(app(xs, Cons(x, Nil))) == x
; branch : xs = Cons(_h, t), t = Cons(_h2, _t2)
;
; definitions:
;   app(Nil, y)                 = y
;   app(Cons(h, t), y)          = Cons(h, app(t, y))
;   last(Nil)                   = Z
;   last(Cons(h, Nil))          = h
;   last(Cons(h, Cons(h2, t2))) = last(Cons(h2, t2))

(declare-sort Nat 0)
(declare-sort NList 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Nil NList)
(declare-fun Cons (Nat NList) NList)
(declare-fun app (NList NList) NList)
(declare-fun last (NList) Nat)

(declare-const xs NList)
(declare-const x Nat)
(declare-const _h Nat)
(declare-const t NList)
(declare-const _t2 NList)
(declare-const _h2 Nat)

(assert (= xs (Cons _h t)))
(assert (= t (Cons _h2 _t2)))

; instantiated terms:
;   from the goal:
;     (Cons x Nil)   (app xs (Cons x Nil))   (last (app xs (Cons x Nil)))
;   from the hypothesis (last (app t (Cons x Nil))) == x:
;     (app t (Cons x Nil))   (last (app t (Cons x Nil)))
;   from patterns:
;     (Cons _h t)   (Cons _h2 _t2)

(assert (distinct (last (app xs (Cons x Nil))) x))
(check-sat)
