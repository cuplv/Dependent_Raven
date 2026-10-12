---
name: raven-instantiate
description: Repair a failed ravencheck proof by adding missing instantiate!
  hints, read off the countermodel the verifier writes for each failing goal
  (test_suite/logs/<goal>_model.json) against the source program. Use when a
  test_suite proof fails with "solver found counterexamples". Adds hints only;
  when the model shows the failure is not a missing hint, reports which of
  three tells it is (lemma / case split / guard that must hold) instead.
---

# raven-instantiate

## 1. Contract

The ONLY edit is adding `instantiate!(...)` lines inside the failing arm of
the failing lemma. Specs, definitions, match skeletons, recursive and helper
calls, other tests: read-only. Never weaken a spec, comment out a property or
ignore a test. Hints are never removed while the proof is red, and after green
only on the keyword `minimize`. If no hint can succeed, the output is a report
(§8), not a forced green.

A hint is always sound: `instantiate!(t)` says the application `t` has a value,
true of every real (total) function. The only risk is a wasted round.

## 2. Inputs

- the source `test_suite/tests/<file>.rs`: definitions, and the failing
  lemma whose `match` arms are the branches;
- the model `test_suite/logs/<lemma>_vc_<k>_model.json`, written for every
  goal the solver answers `sat`.

Run from the repository root: `cargo test -p test_suite --test <file>`. One
run reports every failing goal. Logs are keyed by lemma name, so two files
sharing a lemma name overwrite each other's logs. A goal reported `UNKNOWN`
has no model: report it as such and stop on it.

## 3. Reading the model

- `f: (a…) → r` means `f(a…)` is defined with value `r`. An **absent row**
  means the application is undefined; no equation mentioning it can fire.
  That absence is the only fact this skill acts on.
- Rows exist for named terms (goal, hypotheses, hints), for equations with no
  inner term (`add(Z, y) = y` gives `(Z, y) → y` for every `y`), or
  arbitrarily. Which is which does not matter.
- An element that is the output of a constructor row has a known shape; one
  that is the output of none is **junk**. A junk result at an application
  whose argument shape is known is an equation that could not fire.
- The **branch** is the set of constructor rows tying pattern variables to
  goal variables (`Cons: (_h, t) → xs`). A variable with no such row is one
  the branch does not fix.

Details: `reference/model-format.md` (open only if a row is ambiguous).

## 4. The walk — per failing goal, on its own model

1. Substitute the variables' elements into the `Lemma`; note which side or
   hypothesis the model refutes.
2. For each application whose row is junk (or wrong for the goal), take the
   equation of its definition that this branch selects — the constructor
   cases the branch fixes pick the arm — and list its **inner terms**: the
   applications on the right-hand side and, for an `if`, the guard.
3. Look each inner term up. Row present → recurse (step 2). Row **absent
   with arguments the branch fixes** → candidate (§5). Absent because an
   argument is a variable the branch does not fix → a stop tell (§5).
4. Add every candidate of every failing goal, re-run once, re-read. Each
   round exposes one more level; a new absent row on the walk is progress;
   stop when a model shows none.

## 5. Candidates and stop tells

| What the model shows | Verdict | Action |
|---|---|---|
| an inner term of the selected equation has no row (`app(t2, [x])` under `t = Cons(_h2, t2)`; `take_a(n', t)`; a constructor term such as `P(h, h2)` when the whole `P` table is absent) | **inner term** | hint it |
| the `if`'s guard has no row and *either* value closes the arm (one outcome by the goal or a hypothesis, the other by the IH) | **guard, must exist** | hint it |
| the stuck application's recursion argument is a tag the branch does not fix, and the goal equates the application with something else (`app(t, Nil) = NList!3`, `t = NList!1`) | **algebraic** | stop: a lemma is missing |
| the next equation matches on a variable that is a tag the branch does not fix (`last(Cons(_h, t))`, `t` the output of no `Cons` row) | **shape** | stop: a case split is missing |
| the guard row is missing and only one value closes the goal, on such a variable (`eq_nat(x, x)` must be true; `eq_nat(x, y)` must be false under `lt(x, y)`) — naming it lets the solver pick the wrong value | **guard, must hold** | stop: a lemma about the guard is missing |

On a tell: add no hint for that goal, finish the other goals' candidates, and
report the tell with the two or three model rows that show it.

## 6. The walk in twenty lines

`add(S(S(Z)), x) == S(S(x))`, empty body, with `add(Z, y) = y` and
`add(S(x'), y) = S(add(x', y))`. Model:

```json
"x": "Nat!3",
"S":   { "Z": "Nat!1", "Nat!1": "Nat!2", "Nat!3": "Nat!5", "Nat!5": "Nat!6" },
"add": { "(Nat!2, Nat!3)": "Nat!4", "(Z, Nat!1)": "Nat!1", "(Z, Nat!3)": "Nat!3", ... }
```

Shapes: `Nat!1 = S(Z)`, `Nat!2 = S(S(Z))`, `Nat!5 = S(x)`, `Nat!6 = S(S(x))`;
`Nat!4` is junk. Goal: `add(Nat!2, Nat!3) = Nat!4 ≠ Nat!6`.

| application | row? | equation → inner terms | verdict |
|---|---|---|---|
| `add(S(S(Z)), x)` = `(Nat!2, Nat!3)` | `Nat!4`, junk | `add(S(x'), y) = S(add(x', y))` → `add(S(Z), x)` | follow |
| `add(S(Z), x)` = `(Nat!1, Nat!3)` | **absent** | — | **candidate** |

Edit: `instantiate!(add(Nat::S(Nat::Z), x));` — green next round (the next
level, `add(Z, x)`, is a universal row).

## 7. Edit conventions

- `instantiate!` contents are recorded, not compiled: no `Box::new`, no
  `.clone()`, no ownership concerns inside the macro.
- Use the binder names in scope in the failing arm; rename a `_`-prefixed
  binder (`_h2` → `h2`) when a hint needs it.
- Place hints in the failing arm, before its recursive or helper call.

## 8. Report

Green: the hints added, by round and branch. A tell: the goal, the branch,
the tell's name, the model rows that show it, and the fact or case split the
proof appears to need — with no edit made for it.

## 9. What to open, and when

Nothing by default. `reference/model-format.md` if a row is ambiguous. One
example when its situation arises: `0-the-walk` (unsure how to start),
`1-two-guards` (several guards in one arm), `2-inner-term-fixed-constructor`
(junk below a fixed constructor), `3-two-branches-constructor-terms` (two
failing goals, constructor-typed inner terms), `4-nested-rounds` (a second
round finds a deeper absent row), `5-hand-off` (before reporting a tell, match
it against the three there). With the invocation keyword `verbose`, read
examples 0 and 2 before the first walk. `fixtures/MANIFEST.md` says how each
example's model was produced.
