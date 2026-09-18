# Example 6 — Depth chain: a conditional preservation lemma, and depth accounting

The intake state: induction hypothesis present, one PROVEN helper
(le_neg) already in the module, frontier saturated (the hint is the
instantiate procedure's work) — still failing. The missing piece is a
CONDITIONAL lemma (the property propagates through a function), and its
construction demonstrates the lemma-depth accounting: the new conjecture
costs one depth unit; calling the already-proven le_neg inside it costs
none.

## Broken proof

`tip_78` (`sorted(sort(xs))`), with `sort(Cons(h,t)) = insort(h, sort(t))`:

```rust
fn tip_78(xs: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(h, t) => {
            instantiate!(insort(h, sort(t)));   // saturation's work
            tip_78(*t)
        }
    }
}
```

```
$ cargo test --test prop_78_chain_gap
## > Failed to verify 'tip_78_vc_6': solver found counterexamples.
```

## Counterexample (the ledger)

```smt2
; branch : xs = Cons(h, t)
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
```

## Classify

Coverage: `goal[xs := t]` = `sorted(sort(t))` — present. Saturation:
confirmed — `sort(xs)` unfolded (its result `insort(h, sort(t))` is the
hint), and nothing further pins: `insort(h, sort(t))`'s scrutinee
`sort(t)` is an opaque application with no derivable shape. Guard: no
guard term is reachable (the guarded arms sit behind the unpinnable
scrutinee).

Shape-lemma recipe first (nearest signature): which constructor form
must `insort(h, sort(t))` take? It STALLS — insort's result head depends
on a comparison (`Cons(h, ...)` or `Cons(head-of-sort(t), ...)`); no
single constructor form suffices. When the backward-shape derivation
stalls, fall through to the PRESERVATION pattern: relate the goal atom
to the nearest hypothesis atom.

```
goal atom:        sorted( insort(h, A) )      where A = sort(t)
hypothesis atom:  sorted( A )
```

Anti-unify: the goal is the hypothesis's property, applied to the SAME
list after an `insort`. The candidate is conditional — the hypothesis
must feed it:

```
candidate:  forall x, a.  implies(sorted(a), sorted(insort(x, a)))
```

## Pre-validate — HISTORICAL: probes are no longer performed (SKILL.md §1 "Inputs", §4 step 4); read this section as the reasoning behind the candidate, not as a step to repeat

The instance's antecedent (`sorted(sort(t))`) is already true in the
context, so probe the consequent:

```smt2
(declare-const st UI_NList)   (assert (sort_rel t st))
(declare-const iw UI_NList)   (assert (insort_rel h st iw))
(declare-const sv Bool)       (assert (sorted_rel iw sv))
(assert (= sv true))
(check-sat)      ; -> unsat
```

Validated.

## Construct — and the depth accounting

The candidate is a substantial conjecture (it is TIP prop_77). Its
construction opens ONE unit of lemma depth:

```
tip_78  ->  sorted_insort        NEW conjecture: depth 1
                └─ calls le_neg  ALREADY PROVEN in the module: depth 0
```

Calling a proven lemma costs no depth — depth counts stacked UNPROVEN
conjectures only. Had `le_neg` also been missing, its construction
inside `sorted_insort`'s proof would open depth 2 (the default budget
is 3; overridable via `depth-limit N`).

The helper (guard-split proof over the tail's shape; its internal hints
are the instantiate-composition product of its own branches) and the
call at the validated instance's arguments:

```rust
    #[val((x: Nat, xs: NList) -> Lemma(implies(sorted(xs), sorted(insort(x, xs)))))]
    fn sorted_insort(x: Nat, xs: NList) { ... }   // the prop_77 proof:
        // Nil branch: two hints; Cons branch: le_neg(x, h) + the insort
        // unfolding hints + a nested match on the tail with its hints
        // and the recursive call sorted_insort(x, *t) [descent: t ⊏ xs]
```

```rust
        NList::Cons(h, t) => {
            instantiate!(insort(h, sort(t)));
            sorted_insort(h.clone(), sort(*t.clone()));
            tip_78(*t)
        }
```

Note the call's second argument is an EXPRESSION (`sort(*t.clone())`) —
the instance from pre-validation, transcribed. Acyclicity:
`sorted_insort` calls `le_neg` and itself (descent: `t ⊏ xs`); neither
calls `tip_78`.

## Compose

`sorted_insort`'s own proof needs its internal hints — applying the
instantiate procedure branch by branch (this is the raven-instantiate
skill's world, at scale: the measured-minimal set is 8 hints across
three branches — two guards, two insort outcomes, four sorted-at-value
switches). With them, the helper verifies; see the answer key
`tests/prop_78.rs` for the final form.

## Verified

```
$ cargo test --test prop_78_chain_gap
test result: ok. 1 passed; 0 failed
```

Minimization: the saturation-era hint `insort(h, sort(t))` is redundant
once the helper call's postcondition mentions the same term. Removed:
still green — the final Cons branch is exactly two calls, no hints.

Report: one new lemma (preservation signature, conditional), depth used
1 of 3; one call at an expression instance; le_neg reused at depth 0;
one stale hint removed.
