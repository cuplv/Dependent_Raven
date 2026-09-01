# Example 2 — Parallel hints: sibling terms in one branch, several candidates

One frontier round can yield SEVERAL candidates: here two applications of
the same function with different arguments both unfold under the same
branch, and both wrapped results are missing. All candidates from a round
are added together.

## Broken proof

`tip_eight` (TIP prop_08): induction skeleton and induction hypothesis
intact; both hints missing.

```rust
#[val((i: Nat, j: Nat, k: Nat) -> Lemma(sub(add(i,j), add(i,k)) == sub(j, k)))]
fn tip_eight(i: Nat, j: Nat, k: Nat) {
    match i {
        Nat::Z => (),
        Nat::S(i_prime) => {
            tip_eight(*i_prime, j, k);
        }
    }
}
```

```
$ cargo test --test prop_08
## > Failed to verify 'tip_eight_vc_5': solver found counterexamples.
## > 💾 Counterexample: logs/tip_eight_vc_5_counterexample.smt2
```

## Counterexample

```smt2
; ravencheck counterexample
; lemma  : tip_eight   [vc 5]
; goal   : sub(add(i, j), add(i, k)) == sub(j, k)
; branch : i = S(i_prime)
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

(declare-const k Nat)
(declare-const i Nat)
(declare-const j Nat)
(declare-const i_prime Nat)

(assert (= i (S i_prime)))

; instantiated terms:
;   from the goal:
;     (sub j k)   (add i j)   (add i k)   (sub (add i j) (add i k))
;   from the hypothesis (sub (add i_prime j) (add i_prime k)) == (sub j k):
;     (add i_prime j)   (add i_prime k)   (sub (add i_prime j) (add i_prime k))
;   from patterns:
;     (S i_prime)

(assert (distinct (sub (add i j) (add i k)) (sub j k)))
(check-sat)
```

## Reasoning

**Coverage pre-check.** The branch binds `i_prime`; the hypothesis group
mentions it (the recursive call on `i_prime`). Not a missing-recursive-call
failure. Proceed.

**Frontier round.**

| Ledger application | Scrutinee(s) | Shape known? | One-step result | Absent terms |
|---|---|---|---|---|
| `(add i j)` | `i` (add matches arg 1) | yes: `i = S(i_prime)` | `S(add(i_prime, j))` | **`S(add(i_prime, j))`** |
| `(add i k)` | `i` | yes: `i = S(i_prime)` | `S(add(i_prime, k))` | **`S(add(i_prime, k))`** |
| `(sub (add i j) (add i k))` | `add(i, j)`, `add(i, k)` — function results, no shape | no | — | — |
| `(sub j k)` | `j` — bare variable | no | — | — |
| hypothesis-group terms | scrutinees `i_prime`, `j` — bare variables | no | — | — |

No `if` in either definition, so no guard-term candidates.

**Result: two candidates from sibling terms.** `add(i, j)` and `add(i, k)`
are distinct applications that BOTH unfold under the same branch fact
`i = S(i_prime)`; each needs its own wrapped result defined. They are not
alternatives — the goal's left side mentions both, so the proof needs both:
with only one added, one side of `sub(add(i,j), add(i,k))` still floats
free and the VC keeps failing. Add every candidate the round produced.

## Fix

Both hints in the failing branch, before the recursive call:

```rust
        Nat::S(i_prime) => {
            instantiate!(Nat::S(add(i_prime, j)));
            instantiate!(Nat::S(add(i_prime, k)));
            tip_eight(*i_prime, j, k);
        }
```

## Verified

```
$ cargo test --test prop_08
test tip_benchmarks_tests::check_properties ... ok
```

Minimization check: removing either hint alone re-breaks the proof — both
are needed; keep both.
