# Example 1 — Wrapped constructor: one pinned unfolding, one missing hint

The canonical case. A pinned application unfolds to a constructor-wrapped
term that has no definedness switch; that term IS the missing hint.

## Broken proof

`tip_nine` (TIP prop_09): the induction skeleton and the induction
hypothesis call are correct; only the hint is missing.

```rust
#[val((i: Nat, j: Nat, k: Nat) -> Lemma(sub(sub(i, j), k) == sub(i, add(j, k))))]
fn tip_nine(i: Nat, j: Nat, k: Nat) {
    match i {
        Nat::Z => (),
        Nat::S(i_prime) => match j {
            Nat::Z => (),
            Nat::S(j_prime) => {
                tip_nine(*i_prime, *j_prime, k);
            }
        },
    }
}
```

```
$ cargo test --test prop_09
## > Failed to verify 'tip_nine_vc_6': solver found counterexamples.
## > 💾 Counterexample: logs/tip_nine_vc_6_counterexample.smt2
```

## Counterexample

```smt2
; ravencheck counterexample
; lemma  : tip_nine   [vc 6]
; goal   : sub(sub(i, j), k) == sub(i, add(j, k))
; branch : i = S(i_prime), j = S(j_prime)
;
; definitions:
;   add(Z, y)               = y
;   add(S(x_prime), y)      = S(add(x_prime, y))
;   sub(Z, y)               = Z
;   sub(S(x_min), Z)        = S(x_min)
;   sub(S(x_min), S(y_min)) = sub(x_min, y_min)

(declare-sort Nat 0)
(declare-const Z Nat)
(declare-fun S (Nat) Nat)
(declare-fun add (Nat Nat) Nat)
(declare-fun sub (Nat Nat) Nat)

(declare-const i Nat)
(declare-const j Nat)
(declare-const k Nat)
(declare-const i_prime Nat)
(declare-const j_prime Nat)

(assert (= i (S i_prime)))
(assert (= j (S j_prime)))

; instantiated terms:
;   from the goal:
;     (sub i j)   (sub (sub i j) k)   (add j k)   (sub i (add j k))
;   from the hypothesis (sub (sub i_prime j_prime) k) == (sub i_prime (add j_prime k)):
;     (sub i_prime j_prime)   (sub (sub i_prime j_prime) k)   (add j_prime k)   (sub i_prime (add j_prime k))
;   from patterns:
;     (S i_prime)   (S j_prime)

(assert (distinct (sub (sub i j) k) (sub i (add j k))))
(check-sat)
```

## Reasoning

**Coverage pre-check.** The branch line binds `i_prime` and `j_prime`, and
the ledger has a hypothesis group mentioning both (the recursive call
`tip_nine(i_prime, j_prime, k)`). No pattern variable is missing from the
hypotheses — this is not a missing-recursive-call failure. Proceed.

**Frontier round.** For each application in the ledger, check whether its
scrutinee's constructor shape is known (from the branch line or a literal
constructor argument), and if so unfold it one step using the definitions
block; every result term absent from the ledger is a candidate.

| Ledger application | Scrutinee(s) | Shape known? | One-step result | Absent terms |
|---|---|---|---|---|
| `(sub i j)` | `i`, then `j` (sub matches arg 1, then arg 2) | yes: `S(i_prime)`, `S(j_prime)` | `sub(i_prime, j_prime)` | none — in ledger |
| `(sub (sub i j) k)` | `sub(i, j)` — a function result, no shape | no | — | — |
| `(add j k)` | `j` (add matches arg 1) | yes: `j = S(j_prime)` | `S(add(j_prime, k))` | **`S(add(j_prime, k))`** (`add(j_prime, k)` itself is in the ledger) |
| `(sub i (add j k))` | `i` yes, but inner scrutinee `add(j, k)` has no shape | no | — | — |
| hypothesis-group terms | scrutinees are bare variables (`i_prime`, `j_prime`) | no | — | — |

Neither `add` nor `sub` has an `if` in its body, so there are no guard-term
candidates.

**Result: exactly one candidate — `S(add(j_prime, k))`.** Why it is the
failure: add's S-equation can only conclude `add(j, k) = S(add(j_prime, k))`
if the output term has a definedness switch; without it the equation is
silently vacuous, `add(j, k)`'s value floats free of anything S-shaped, and
the right-hand side of the goal never connects to the left.

## Fix

Add the candidate as a hint in the failing branch (the `i = S`, `j = S` arm),
before the recursive call:

```rust
            Nat::S(j_prime) => {
                instantiate!(Nat::S(add(j_prime, k)));
                tip_nine(*i_prime, *j_prime, k);
            }
```

## Verified

```
$ cargo test --test prop_09
test tip_benchmarks_tests::check_properties ... ok
```

One hint, one round. Minimization is trivial (a single hint that is needed).
