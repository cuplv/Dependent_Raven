# Example 4 — Missing recursive call: the coverage check, done right

The intake state: helper lemma present and called, left induction
hypothesis present, frontier saturated (the third hint is the
instantiate procedure's work) — still failing. The missing piece is a
recursive call, and this example shows why the coverage check must look
for the INSTANTIATED GOAL, not merely for the variable's name.

## Broken proof

`tip_47` (`height(mirror(t)) == height(t)`), Node branch:

```rust
Tree::Node(l, e, r) => {
    instantiate!(Tree::Node(Box::new(mirror(r)), e, Box::new(mirror(l))));
    instantiate!(Nat::S(max(height(l), height(r))));
    instantiate!(Nat::S(max(height(mirror(r)), height(mirror(l)))));  // saturation's work
    tip_47(*l.clone()); // induction hypothesis, left subtree
    max_comm(height(*l), height(*r));
}
```

```
$ cargo test --test prop_47_ih_gap
## > Failed to verify 'tip_47_vc_19': solver found counterexamples.
```

## Counterexample (the ledger)

```smt2
; branch : t = Node(l, e, r)
; instantiated terms:
;   from the goal:
;     (mirror t)   (height (mirror t))   (height t)
;   from the hypothesis (height (mirror l)) == (height l):
;     (mirror l)   (height (mirror l))   (height l)
;   from the hypothesis (max (height l) (height r)) == (max (height r) (height l)):
;     (height r)   (max (height l) (height r))   (max (height r) (height l))
;   from patterns:
;     (Node l e r)
;   user hints (instantiate!):
;     (Node (mirror r) e (mirror l))   (S (max (height l) (height r)))
;     (S (max (height (mirror r)) (height (mirror l))))
```

## Classify — the refined coverage check

The TRAP first: `r` DOES appear in a hypothesis group (the helper's fact
mentions `height r`), so the naive check "is each branch variable
mentioned by some hypothesis?" passes — and misses the gap. Being
mentioned by SOME fact is not the same as being covered by an INDUCTION
HYPOTHESIS.

The robust check: for each branch-bound variable whose sort matches a
lemma parameter (here `l, r : Tree` match `t : Tree`), ask whether the
GOAL INSTANTIATED AT THAT VARIABLE appears among the hypothesis facts:

```
goal[t := l]:  (height (mirror l)) == (height l)   -- present (group 1)
goal[t := r]:  (height (mirror r)) == (height r)   -- ABSENT
```

**Missing recursive call on `r`.** (Checked before all other signatures —
it is the cheapest fix. Note the ledger corroborates: `height (mirror r)`
appears only inside the saturation hint, connected to nothing.)

## Candidate

Not a new lemma — the instance `height(mirror(r)) == height(r)` of the
target's own statement, obtained by a recursive call on `r`.

## Pre-validate — HISTORICAL: probes are no longer performed (SKILL.md §1 "Inputs", §4 step 4); read this section as the reasoning behind the candidate, not as a step to repeat

```smt2
(declare-const mr UI_Tree)   (assert (mirror_rel r mr))
(declare-const hmr UI_Nat)   (assert (height_rel mr hmr))
(declare-const hr UI_Nat)    (assert (height_rel r hr))
(assert (= hmr hr))
(check-sat)      ; -> unsat
```

Validated: with the helper's fact already in context, the IH instance
alone closes the VC. (Historical note: with the helper ALSO missing,
this same probe stays `sat` — each fact alone is insufficient, only the
pair closes. Single-candidate probing then exhausts and stops; the
coverage check existing as a SEPARATE, earlier stage is what keeps that
two-gap scenario diagnosable: fix the IH first, then the algebraic
candidate validates.)

## Construct — a descent-checked self-call

```rust
    tip_47(*l.clone()); // induction hypothesis, left subtree
    tip_47(*r.clone()); // induction hypothesis, right subtree
```

**Descent check (mandatory for every added self-call):** the argument
`r` is a pattern-bound strict subterm of the parameter `t` (bound by
`Node(l, e, r)` matching `t`); one argument, strictly smaller — the
call is a sound structural induction. A self-call failing this check
(e.g. `tip_47(t.clone())` — same argument, which would "prove" anything)
is forbidden, no matter what pre-validation says.

**Report line (mandatory):** `added tip_47(*r): r ⊏ t via Node(l, e, r)`.

## Compose

Not needed: the added statement is a call, not a new lemma — there is no
helper proof to grind.

## Verified

```
$ cargo test --test prop_47_ih_gap
test result: ok. 1 passed; 0 failed
```

Minimization: with the IH present, the saturation-era hint
`S(max(height(mirror(r)), height(mirror(l))))` is redundant (its element
now rides the helper's equality and hint 2). Removed: still green.

Report: no new lemma; one recursive call on `r` (descent: `r ⊏ t`), one
stale hint removed.
