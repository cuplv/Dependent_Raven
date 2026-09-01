; ravencheck counterexample
; lemma  : app_assoc   [vc 5]
; goal   : app(app(x, y), z) == app(x, app(y, z))
; branch : x = Cons(h, t)
;
; definitions:
;   app(Nil, y)        = y
;   app(Cons(h, t), y) = Cons(h, app(t, y))

(declare-sort Elem 0)
; sort 'List' is written as 'List_' below (the name collides with a Z3 built-in)
(declare-sort List_ 0)
(declare-const Nil List_)
(declare-fun Cons (Elem List_) List_)
(declare-fun app (List_ List_) List_)

(declare-const x List_)
(declare-const z List_)
(declare-const y List_)
(declare-const h Elem)
(declare-const t List_)

(assert (= x (Cons h t)))

; instantiated terms:
;   from the goal:
;     (app y z)   (app x y)   (app (app x y) z)   (app x (app y z))
;   from the hypothesis (app (app t y) z) == (app t (app y z)):
;     (app t y)   (app (app t y) z)   (app t (app y z))
;   from patterns:
;     (Cons h t)

(assert (distinct (app (app x y) z) (app x (app y z))))
(check-sat)
