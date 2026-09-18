# Example 1 — Guard lemma: the guard is defined, but nothing pins its value

The intake state: the instantiate procedure already ran to saturation —
the guard term has its switch — and the proof still fails. The missing
piece is a FACT about the guard's value, generalized into a helper lemma.

## Broken proof

`tip_04`: the guard switch in the body is the instantiate procedure's
work; the frontier is saturated (the guard's own scrutinees are bare
variables — nothing further unfolds).

```rust
#[val((n: Nat, xs: NList) -> Lemma(Nat::S(Box::new(count(n, xs))) == count(n, NList::Cons(n, Box::new(xs)))))]
fn tip_04(n: Nat, xs: NList) {
    instantiate!(eq_nat(n, n));
}
```

```
$ cargo test --test prop_04_lemma_gap
## > Failed to verify 'tip_04_vc_3': solver found counterexamples.
## > 💾 Counterexample: logs/tip_04_vc_3_counterexample.smt2
```

## Counterexample

```smt2
; ravencheck counterexample
; lemma  : tip_04   [vc 3]
; goal   : S(count(n, xs)) == count(n, Cons(n, xs))
;
; definitions:
;   count(x, Nil)              = Z
;   count(x, Cons(h, t))       = if eq_nat(x, h) then S(count(x, t)) else count(x, t)
;   eq_nat(Z, Z)               = true
;   eq_nat(Z, S(_y_min))       = false
;   eq_nat(S(x_min), Z)        = false
;   eq_nat(S(x_min), S(y_min)) = eq_nat(x_min, y_min)

(declare-sort Nat 0)
(declare-sort NList 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Nil NList)
(declare-fun Cons (Nat NList) NList)
(declare-fun count (Nat NList) Nat)
(declare-fun eq_nat (Nat Nat) Bool)

(declare-const xs NList)
(declare-const n Nat)

; instantiated terms:
;   from the goal:
;     (count n xs)   (S (count n xs))   (Cons n xs)   (count n (Cons n xs))
;   user hints (instantiate!):
;     (eq_nat n n)

(assert (distinct (S (count n xs)) (count n (Cons n xs))))
(check-sat)
```

## Classify

Coverage: no branch line, no pattern variables — nothing to check.
Saturation: confirmed (the only pinned unfolding, count at the literal
`Cons(n, xs)`, mentions guard `eq_nat(n, n)` [present] and results
`S(count(n, xs))` / `count(n, xs)` [present]; `eq_nat(n, n)`'s own
scrutinees are bare variables — the frontier is empty).

Signature test, in cost order: missing IH — no. **Guard lemma — YES:
the guard term `(eq_nat n n)` is PRESENT in the ledger and the proof
still fails.** The countermodel is free to make the guard false, which
disables the then-equation and lets `count(n, Cons(n, xs))` collapse
away from `S(count(n, xs))`. The missing fact is the guard's value.

## Candidate

Which value does the proof need? The goal wants the THEN-equation to fire
(`count(n, Cons(n, xs)) == S(count(n, xs))` is the goal's own right-left
bridge), so the fact is `eq_nat(n, n) == true`.

Generalize minimally — same constant, same variable: both occurrences of
`n` are the SAME skolem, so they become one variable:

```
candidate:  forall x.  eq_nat(x, x)          (reflexivity)
```

(The per-occurrence generalization `forall x, y. eq_nat(x, y)` is FALSE —
never generalize two occurrences of the same constant to different
variables unless the instance demands it.)

## Pre-validate — HISTORICAL: probes are no longer performed (SKILL.md §1 "Inputs", §4 step 4); read this section as the reasoning behind the candidate, not as a step to repeat

Assert the candidate's instance on the failed query
(`logs/tip_04_vc_3_failed_query.smt2`):

```smt2
(declare-const b Bool)
(assert (eq_nat_rel n n b))
(assert (= b true))
(check-sat)      ; -> unsat
```

`unsat`: this fact closes the VC — the candidate is worth proving.
(Contrast: probing the wrong candidate `count(n, Cons(n, xs)) ==
count(n, xs)` gives `sat` — the countermodel already satisfies it, so it
can close nothing. A useful lemma must CONTRADICT the countermodel.)

## Construct

Helper from the single-variable structural-induction template, plus its
call in the failing proof:

```rust
    // Helper: eq_nat is reflexive.
    #[val((x: Nat) -> Lemma(eq_nat(x, x)))]
    fn eq_refl(x: Nat) {
        match x {
            Nat::Z => (),
            Nat::S(x_min) => eq_refl(*x_min),
        }
    }
```

```rust
    fn tip_04(n: Nat, xs: NList) {
        instantiate!(eq_nat(n, n));
        eq_refl(n);
    }
```

Envelope check: one new Lemma item + one statement in the target's proof
body. The target's spec and every function definition untouched.
Acyclicity: `eq_refl` calls only itself, on the structurally smaller
`*x_min`.

## Compose

`eq_refl`'s own proof verifies as written — both branches close
definitionally (Z: `eq_nat(Z, Z) = true`; S: the S-S equation plus the
recursive call's postcondition). No instantiate-procedure pass needed on
the helper this time.

## Verified

```
$ cargo test --test prop_04_lemma_gap
test result: ok. 1 passed; 0 failed
```

Minimization: with `eq_refl(n)` present, its postcondition supplies the
term `eq_nat(n, n)` automatically — the manual `instantiate!` line is now
redundant. Removing it: still green. Final proof body: `eq_refl(n);`
alone. Report: one helper (guard signature), one call, zero hints.
