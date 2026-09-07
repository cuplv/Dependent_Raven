# Example 2 — Algebraic lemma: endpoints differ by an argument permutation

The intake state: both induction hypotheses present (coverage passes),
the frontier saturated (the third hint is the instantiate procedure's
work), the proof still failing. The two goal sides evaluate to terms
identical up to swapping one function's arguments — the missing fact is
that function's commutativity. This example also exercises the COMPOSE
stage for real: the constructed helper's own proof needs instantiations.

## Broken proof

`tip_47` (`height(mirror(t)) == height(t)`), Node branch:

```rust
Tree::Node(l, e, r) => {
    instantiate!(Tree::Node(Box::new(mirror(r)), e, Box::new(mirror(l))));
    instantiate!(Nat::S(max(height(l), height(r))));
    instantiate!(Nat::S(max(height(mirror(r)), height(mirror(l)))));  // saturation's work
    tip_47(*l.clone()); // induction hypothesis, left subtree
    tip_47(*r.clone()); // induction hypothesis, right subtree
}
```

```
$ cargo test --test prop_47_lemma_gap
## > Failed to verify 'tip_47_vc_16': solver found counterexamples.
```

## Counterexample (the ledger and header; full file in fixtures/)

```smt2
; branch : t = Node(l, e, r)
; instantiated terms:
;   from the goal:
;     (mirror t)   (height (mirror t))   (height t)
;   from the hypothesis (height (mirror l)) == (height l):
;     (mirror l)   (height (mirror l))   (height l)
;   from the hypothesis (height (mirror r)) == (height r):
;     (mirror r)   (height (mirror r))   (height r)
;   from patterns:
;     (Node l e r)
;   user hints (instantiate!):
;     (Node (mirror r) e (mirror l))   (S (max (height l) (height r)))
;     (S (max (height (mirror r)) (height (mirror l))))
```

## Classify

Coverage: branch binds `l`, `e`, `r`; hypothesis groups exist for both
`l` and `r` — no missing recursive call. Saturation: confirmed (every
pinned unfolding's terms are in the ledger; the remaining scrutinees —
`height(l)`, `height(r)` and friends — are shapeless, so nothing more
unfolds). Guard: no `if`-guards among these definitions.

**Algebraic — YES.** Evaluate both sides through the ledger's facts:

```
LHS  height(mirror(t)) = S(max(height(mirror(r)), height(mirror(l))))
                       = S(max(height(r), height(l)))        [both IHs]
RHS  height(t)         = S(max(height(l), height(r)))
```

Fully computed endpoints, differing ONLY by the order of `max`'s
arguments.

## Candidate

Anti-unify the endpoints: `S(max(A, B))` vs `S(max(B, A))` with
`A = height(r)`, `B = height(l)`. Fresh variables at the disagreement
positions give:

```
candidate:  forall a, b.  max(a, b) == max(b, a)      (commutativity)
```

Rejected alternative — the goal itself as a "lemma"
(`height(mirror(x)) == height(x)`): its instance also probes `unsat`
(trivially — it IS the negated goal's complement), which is exactly why
pre-validation success is NOT sufficient. The acyclicity rule filters
it: a helper may not restate or call the target.

## Pre-validate

```smt2
(declare-const hl UI_Nat)   (assert (height_rel l hl))
(declare-const hr UI_Nat)   (assert (height_rel r hr))
(declare-const m1 UI_Nat)   (assert (max_rel hl hr m1))
(declare-const m2 UI_Nat)   (assert (max_rel hr hl m2))
(assert (= m1 m2))
(check-sat)      ; -> unsat
```

Validated: this fact closes the VC.

## Construct

Two-variable nested-induction template, plus the call at the endpoint
arguments:

```rust
    // Helper: max is commutative.
    #[val((a: Nat, b: Nat) -> Lemma(max(a, b) == max(b, a)))]
    fn max_comm(a: Nat, b: Nat) {
        match a {
            Nat::Z => match b {
                Nat::Z => (),
                Nat::S(_b_min) => (),
            },
            Nat::S(a_min) => match b {
                Nat::Z => (),
                Nat::S(b_min) => {
                    max_comm(*a_min, *b_min);
                }
            },
        }
    }
```

```rust
    tip_47(*r.clone());
    max_comm(height(*l), height(*r));
```

Envelope: one new Lemma item + one call. Acyclicity: `max_comm` calls
only itself on structurally smaller arguments; it neither calls nor
restates `tip_47`.

## Compose — the helper's own proof needs instantiations

```
$ cargo test --test prop_47_lemma_gap
## > Failed to verify 'max_comm_vc_6': solver found counterexamples.
```

The failure moved INTO the helper. Apply the raven-instantiate
procedure to `max_comm_vc_6` — under that skill's envelope, inside the
helper only. Its counterexample's frontier: `max(a, b)` and `max(b, a)`
are pinned (`a = S(a_min)`, `b = S(b_min)`) and their wrapped results
are absent — two candidates:

```rust
                Nat::S(b_min) => {
                    instantiate!(Nat::S(max(a_min, b_min)));
                    instantiate!(Nat::S(max(b_min, a_min)));
                    max_comm(*a_min, *b_min);
                }
```

```
test result: ok. 1 passed; 0 failed
```

## Verified

Minimization: with `max_comm` in place, its postcondition supplies the
swapped max automatically — the saturation-era hint
`S(max(height(mirror(r)), height(mirror(l))))` is now redundant.
Removed: still green. The two original hints stay (each is needed for
the unfolding of `mirror(t)` / `height(t)`).

Report: one helper (algebraic signature, from endpoint anti-unification),
one call, two hints inside the helper (composition), one stale hint
removed from the target.
