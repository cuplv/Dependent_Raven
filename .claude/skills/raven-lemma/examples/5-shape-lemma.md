# Example 5 — Shape lemma: an opaque application blocks the goal's own step

The intake state: induction hypothesis present, frontier empty from
round zero — and the proof fails. Superficially like the case-split
signature (nothing to instantiate), but the blocking scrutinee is an
OPAQUE APPLICATION, not a bare input variable — and that difference
changes the fix entirely: the missing fact is an equation giving the
application a constructor-headed form.

## Broken proof

`tip_69` (`le(n, add(m, n))` — note: a bare-predicate goal):

```rust
fn tip_69(n: Nat, m: Nat) {
    match n {
        Nat::Z => (),
        Nat::S(n_min) => {
            tip_69(*n_min, m);
        }
    }
}
```

```
$ cargo test --test prop_69_shape_gap
## > Failed to verify 'tip_69_vc_4': solver found counterexamples.
```

## Counterexample

```smt2
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

(assert (= n (S n_min)))

; instantiated terms:
;   from the goal:
;     (add m n)   (le n (add m n))
;   from the hypothesis (le n_min (add m n_min)):
;     (add m n_min)   (le n_min (add m n_min))
;   from patterns:
;     (S n_min)

(assert (= (le n (add m n)) false))
```

(A Bool goal: the countermodel makes the atom false.)

## Classify

Coverage: `goal[n := n_min]` = `le(n_min, add(m, n_min))` — present.
Saturation: immediate — `add(m, n)`'s scrutinee is the bare `m` (no
pin), and `le(n, add(m, n))` needs BOTH arguments shaped for its S-S
equation: `n` is pinned but `add(m, n)` is not. Guard: none.

Now the distinction that names this signature. The blocking scrutinee is
`add(m, n)` — an **opaque APPLICATION**, not a bare input variable. A
case split cannot help: splitting on `m` gives, in the `S(m')` arm,
`le(n', add(m', n))` after the steps — which is NOT the induction
hypothesis (`le(n', add(m, n'))`); the split changes the wrong argument.
**SHAPE LEMMA: the missing fact is an equation that rewrites the opaque
application into constructor-headed form.**

## Candidate — derived backwards from the blocked step

Which form must `add(m, n)` take for the goal to step to the IH? The
goal atom `le(S(n_min), add(m, n))` steps by le's S-S equation only if
`add(m, n) = S(w)` for some `w` — and then it steps to `le(n_min, w)`,
which the IH closes exactly when `w = add(m, n_min)`. So the needed
instance, using the branch fact `n = S(n_min)`:

```
add(m, S(n_min)) == S(add(m, n_min))
```

Generalize minimally (pattern variable and parameter become variables):

```
candidate:  forall x, y.  add(x, S(y)) == S(add(x, y))
```

This derivation — "work backwards from the blocked equation to the
constructor form it needs" — is the shape signature's recipe, distinct
from the algebraic signature's endpoint anti-unification.

## Pre-validate

```smt2
(declare-const amn UI_Nat)    (assert (add_rel m n amn))
(declare-const amn2 UI_Nat)   (assert (add_rel m n_min amn2))
(declare-const s UI_Nat)      (assert (Nat__S_rel amn2 s))
(assert (= amn s))
(check-sat)      ; -> unsat
```

Validated.

## Construct

Right-argument-family template (induction on the FIRST argument, since
that is where `add` recurses), call at the instance's arguments:

```rust
    // Helper: add(x, S(y)) == S(add(x, y)).
    #[val((x: Nat, y: Nat) -> Lemma(add(x, Nat::S(Box::new(y))) == Nat::S(Box::new(add(x, y)))))]
    fn add_succ_r(x: Nat, y: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => {
                add_succ_r(*x_min, y)
            }
        }
    }
```

```rust
        Nat::S(n_min) => {
            add_succ_r(m.clone(), *n_min.clone());
            tip_69(*n_min, m);
        }
```

Envelope: one new Lemma item + one call. Acyclicity/descent:
`add_succ_r` calls only itself on `*x_min` ⊏ `x`.

## Compose

Not needed: the bare helper verifies as written — both branches close
definitionally plus the IH. (The answer key `tests/prop_69.rs` carries a
hint inside the helper — `instantiate!(Nat::S(add(x_min, Nat::S(y))))` —
measured redundant.)

## Verified

```
$ cargo test --test prop_69_shape_gap
test result: ok. 1 passed; 0 failed
```

Report: one helper (shape signature, derived backwards from the blocked
le-step), one call, zero hints anywhere.
