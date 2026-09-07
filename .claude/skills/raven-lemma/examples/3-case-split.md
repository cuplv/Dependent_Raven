# Example 3 — Case split: empty frontier, goal stuck on a bare input variable

The intake state: the instantiate procedure found NOTHING to add — the
frontier was empty from the very first round — and the proof fails. The
missing piece is not a term and not a lemma: it is proof STRUCTURE, a
case split on the shapeless input that blocks every unfolding.

## Broken proof

`tip_seven` (`sub(add(n, m), n) == m`), failing in its `n = Z` branch:

```rust
fn tip_seven(n: Nat, m: Nat) {
    match n {
        Nat::Z => (),
        Nat::S(n_prime) => {
            instantiate!(Nat::S(add(n_prime, m)));
            tip_seven(*n_prime, m);
        }
    }
}
```

```
$ cargo test --test prop_07_case_gap
## > Failed to verify 'tip_seven_vc_1': solver found counterexamples.
```

## Counterexample

```smt2
; lemma  : tip_seven   [vc 1]
; goal   : sub(add(n, m), n) == m
; branch : n = Z
;
; definitions:
;   add(Z, y)               = y
;   add(S(x_prime), y)      = S(add(x_prime, y))
;   sub(Z, y)               = Z
;   sub(S(x_min), Z)        = S(x_min)
;   sub(S(x_min), S(y_min)) = sub(x_min, y_min)

(assert (= n Z))

; instantiated terms:
;   from the goal:
;     (add n m)   (sub (add n m) n)

(assert (distinct (sub (add n m) n) m))
```

Note how SMALL the ledger is: two terms. That is itself a signal.

## Classify

Coverage: the branch `n = Z` binds no pattern variables — vacuous.
Saturation: immediate. The only pinned unfolding is `add(n, m)` at
`n = Z`, whose result is the bare `m` — no new terms. `sub(add(n,m), n)`
cannot unfold: sub matches its FIRST argument, whose class holds only
`m` — no constructor. Frontier empty, round zero.

Signature test: missing IH — no (no variables to cover). Guard — no
guards among these definitions. Shape lemma — the blocking scrutinee is
not an opaque application... it is **`m`, a bare INPUT variable of the
lemma. CASE SPLIT.** The countermodel exploits `m`'s shapelessness: no
`sub` equation applies at a shapeless argument, so `sub(add(n,m), n)`
floats free of `m`.

## Candidate

Not a lemma — a structural edit: split the failing branch on `m`'s
constructors. Each resulting arm pins `m`'s shape, which is exactly what
every blocked equation was waiting for.

## Pre-validate — the shape probe

The case-split analogue of the instance probe: assert each constructor
shape of `m` on the failed query; the split is a verified fix only if
EVERY shape closes the VC.

```smt2
(assert (= m Nat__Z))            (check-sat)   ; -> unsat
---
(declare-const m_prime UI_Nat)
(assert (Nat__S_rel m_prime m))  (check-sat)   ; -> unsat
```

Both shapes `unsat`: the split is validated before any source edit.
(Had one shape stayed `sat`, that arm would carry a genuine remaining
gap — the split alone would not suffice.)

## Construct

Wrap the failing branch's body in the match (restructuring a proof-body
branch is inside the additive envelope; note the named `_m_prime` — a
bare `_` in a constructor pattern is forbidden):

```rust
        Nat::Z => match m {
            Nat::Z => (),
            Nat::S(_m_prime) => (),
        },
```

## Compose

Not needed: both new arms close definitionally (`m = Z`: everything
collapses to `Z`; `m = S(m')`: sub's second equation fires at the now
S-shaped first argument). If an arm had still failed, the instantiate
procedure would run on that arm's new VC — each arm is its own VC with
its own counterexample.

## Verified

```
$ cargo test --test prop_07_case_gap
test result: ok. 1 passed; 0 failed
```

Report: no new lemma; one case split on `m` in the `n = Z` branch, both
arms definitional, zero hints. (The answer key `tests/prop_07.rs`
additionally carries `instantiate!(sub(m, n))` in this branch — measured
redundant; the split alone is the minimal fix.)
