# Example 4 — Guard term: the ledger looks complete, the `if`-guard is the hole

The trap case. Every unfolding RESULT is already instantiated — the ledger
even shows user hints — yet the proof fails. When a pinned arm's body is an
`if`, the frontier's candidates include the GUARD term, and here the guard
is the one term without a switch. Until the guard is defined, both guarded
equations of the arm are silently vacuous in both directions.

## Broken proof

`tip_02` (count distributes over append): induction skeleton, induction
hypothesis, and all four wrapped-value hints intact; only the guard hint is
missing.

```rust
#[val((n: Nat, xs: NList, ys: NList) ->
    Lemma(add(count(n, xs), count(n, ys)) == count(n, app(xs, ys))))]
fn tip_02(n: Nat, xs: NList, ys: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(h, t) => {
            instantiate!(NList::Cons(h, app(t, ys)));
            instantiate!(Nat::S(count(n, app(t, ys))));
            instantiate!(Nat::S(count(n, t)));
            instantiate!(Nat::S(add(count(n, t), count(n, ys))));
            tip_02(n, *t, ys)
        }
    }
}
```

```
$ cargo test --test prop_02
## > Failed to verify 'tip_02_vc_19': solver found counterexamples.
## > 💾 Counterexample: logs/tip_02_vc_19_counterexample.smt2
```

## Counterexample

```smt2
; ravencheck counterexample
; lemma  : tip_02   [vc 19]
; goal   : add(count(n, xs), count(n, ys)) == count(n, app(xs, ys))
; branch : xs = Cons(h, t)
;
; definitions:
;   add(Z, y)            = y
;   add(S(x_min), y)     = S(add(x_min, y))
;   app(Nil, y)          = y
;   app(Cons(h, t), y)   = Cons(h, app(t, y))
;   count(x, Nil)        = Z
;   count(x, Cons(h, t)) = if eq_nat(x, h) then S(count(x, t)) else count(x, t)

(declare-sort Nat 0)
(declare-sort NList 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-const Nil NList)
(declare-fun Cons (Nat NList) NList)
(declare-fun add (Nat Nat) Nat)
(declare-fun app (NList NList) NList)
(declare-fun count (Nat NList) Nat)

(declare-const ys NList)
(declare-const n Nat)
(declare-const xs NList)
(declare-const h Nat)
(declare-const t NList)

(assert (= xs (Cons h t)))

; instantiated terms:
;   from the goal:
;     (count n ys)   (count n xs)   (add (count n xs) (count n ys))   (app xs ys)   (count n (app xs ys))
;   from the hypothesis (add (count n t) (count n ys)) == (count n (app t ys)):
;     (count n t)   (add (count n t) (count n ys))   (app t ys)   (count n (app t ys))
;   from patterns:
;     (Cons h t)
;   user hints (instantiate!):
;     (Cons h (app t ys))   (S (count n (app t ys)))   (S (count n t))   (S (add (count n t) (count n ys)))

(assert (distinct (add (count n xs) (count n ys)) (count n (app xs ys))))
(check-sat)
```

## Reasoning

**Coverage pre-check.** The branch binds `h` and `t`; the hypothesis group
mentions `t`. Not a missing-recursive-call failure. Proceed.

**Frontier round.** count matches on its SECOND argument, and its Cons arm
is an `if` — for an `if`-arm, the one-step result terms are BOTH branch
results AND the guard term.

| Ledger application | Scrutinee | Shape known? | One-step result | Absent terms |
|---|---|---|---|---|
| `(count n xs)` | `xs` (count matches arg 2) | yes: `xs = Cons(h, t)` | guard `eq_nat(n, h)`; then `S(count(n, t))`; else `count(n, t)` | **`eq_nat(n, h)`** (both results are in the ledger) |
| `(app xs ys)` | `xs` | yes: `xs = Cons(h, t)` | `Cons(h, app(t, ys))` | none — already a user hint |
| `(count n (app xs ys))` | `app(xs, ys)` — a function result | no direct shape (its value equals the already-hinted `Cons(h, app(t, ys))`, whose count-arm has the SAME guard `eq_nat(n, h)`) | — | — |
| `(add (count n xs) (count n ys))` | `count(n, xs)` — function result | no | — | — |
| `(count n ys)`, `(count n t)`, `(app t ys)` … | bare variables / function results | no | — | — |

**Result: one candidate — the guard term `eq_nat(n, h)`.** Note what did
NOT happen: no wrapped result is missing. All four S/Cons wraps are already
present as user hints, and a scan that only looks for missing unfolding
RESULTS concludes, wrongly, that the ledger is complete.

Why the guard's absence breaks everything: count's Cons case compiles to
two guarded equations sharing the guard — the then-equation is disabled
unless the guard is defined-and-true, the else-equation unless
defined-and-false. With NO definedness switch on `eq_nat(n, h)`, the model
simply leaves it undefined and BOTH equations hold vacuously: `count(n, xs)`
and `count(n, app(xs, ys))` never connect to anything. The fix does not need
to say which way the guard goes — a bare definedness switch forces the model
to pick a value, and either value lets the corresponding equations fire and
close the goal (verified: adding just the witness `eq_nat_rel(n, h, b)` to
the failed query flips it from sat to unsat).

## Fix

The guard as a hint in the failing branch:

```rust
        NList::Cons(h, t) => {
            instantiate!(eq_nat(n, h));
            instantiate!(NList::Cons(h, app(t, ys)));
            instantiate!(Nat::S(count(n, app(t, ys))));
            instantiate!(Nat::S(count(n, t)));
            instantiate!(Nat::S(add(count(n, t), count(n, ys))));
            tip_02(n, *t, ys)
        }
```

## Verified

```
$ cargo test --test prop_02
test tip_benchmarks_tests::check_properties ... ok
```

Distinguish this from the missing-LEMMA guard case: here the guard term is
ABSENT from the ledger, and adding its switch alone fixes the proof. If the
guard is PRESENT in the ledger and the proof still fails, no instantiation
will help — that is a missing guard lemma (e.g. a reflexivity or totality
fact about the guard), which is outside this skill's scope: report it and
stop.
