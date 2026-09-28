---
name: raven-instantiate
description: Repair a failed ravencheck proof by adding missing instantiate!
  hints, reading the countermodel the verifier writes for each failing goal
  (test_suite/logs/<goal>_model.json) against the source program. Use when a
  test_suite proof fails with "solver found counterexamples" or "solver
  returned UNKNOWN". Adds hints only; when the model shows the failure is not
  a missing hint, reports which of three tells it is (lemma / case split /
  guard that must hold) instead. Without a model (UNKNOWN, out of memory,
  timeout) it falls back to a frontier search over the instantiated-terms
  ledger the driver writes for every failing goal.
---

# raven-instantiate

## 1. Scope and hard constraints

The ONLY permitted edit is adding `instantiate!(...)` lines inside the failing
branch of the failing lemma. Everything else is read-only: `Lemma(...)`
specifications, function definitions, match skeletons, recursive and helper
calls, other tests. Never weaken a spec, never comment out a property, never
mark a test ignored. Hints are never removed while the proof is red, and after
it is green only if the user asked for minimization (keyword `minimize`). If no
permitted edit can succeed, the correct output is a report (§6), not a forced
green test.

A hint is always sound: `instantiate!(t)` asserts that the application `t` is
defined, which is true of the real (total) functions. The risk of an edit is
never a false proof, only a wasted round.

## 2. Inputs

Two files, nothing else:

- the source: `test_suite/tests/<file>.rs` — definitions and the failing
  lemma, whose `match` arms are the branches;
- the model: `test_suite/logs/<lemma>_vc_<k>_model.json`, written for every
  goal the solver answers `sat`. Format: `reference/model-format.md`.

Run from the repository root: `cargo test -p test_suite --test <file>`. One
run solves every goal and reports every failing one. Log files are keyed by
lemma name; two files sharing a lemma name overwrite each other's logs. A goal
reported `UNKNOWN` (no answer, out of memory, or — once a limit is set — a
timeout) has no model; for it the driver still writes
`logs/<lemma>_vc_<k>_instantiated_terms.smt2`, and the procedure switches to
ledger mode (§7).

## 3. Reading the model

- A row `f: (a…) → r` means `f(a…)` is defined with value `r`. An **absent
  row** means the application is undefined there, so no equation mentioning
  it can fire. That absence is the only fact this skill acts on.
- Rows exist for named terms (goal, hypotheses, hints), for equations with no
  inner term (`add(Z, y) = y` gives `(Z, y) → y` for every `y`), and
  arbitrarily. Which is which does not matter.
- An element that is the output of a constructor row has a known shape; one
  that is the output of none is **junk**. A junk result of a function whose
  argument's shape is known is an equation that could not fire.
- The **branch** is the set of constructor rows tying the pattern variables to
  the goal variables (`Cons: (_h, t) → xs`). A variable the branch does not
  fix is one with no such row.

## 4. The walk

For each failing goal, on its own model:

1. Substitute the variables' elements into the `Lemma` and locate the goal's
   applications; note which side or hypothesis the model refutes.
2. For each application whose row is junk (or whose value is wrong for the
   goal), take the equation of its definition that applies in this branch —
   the constructor cases the branch fixes select it — and list that
   equation's **inner terms**: the applications on its right-hand side and,
   for an `if`, its guard.
3. Look each inner term up. Present → recurse into it (step 2). **Absent, with
   arguments the branch fixes** → a candidate (§5). Absent because an argument
   is a variable the branch does not fix → a stop tell (§6).
4. Collect the candidates of every failing goal, add them all (§7), re-run
   once, and repeat on the new models. Each round exposes one level; new
   absent rows on the walk are progress. Stop when a model shows no new one.

Imitate the tables in `examples/`: application | row? | equation, inner terms
| verdict.

## 5. Candidates — the two things a hint fixes

- **Inner term.** An application on the right-hand side of the applicable
  equation has no row (`app(t2, [x])` under `t = Cons(_h2, t2)`;
  `take_a(n', t)`; a constructor application such as `Pair::P(h, h2)` when the
  whole `P` table is absent). Hint it.
- **Guard that only has to exist.** The guard of the applicable `if` has no
  row, and *either* value lets the branch close (one outcome closes by the
  goal or a hypothesis, the other by the induction hypothesis). Hint it.

Add every candidate of the round, for every failing branch, before one
re-run; do not second-guess or filter.

## 6. Stop tells — when the missing fact is not a hint

- **Algebraic.** The stuck application's recursion argument is a tag the
  branch does not fix, and the goal equates the application with something
  else (`app(t, Nil) = NList!3`, `t = NList!1`). A lemma is missing.
- **Shape.** The next equation matches on a variable that is a tag the branch
  does not fix (`last(Cons(_h, t))`, `t` the output of no `Cons` row). A case
  split is missing.
- **Guard that must hold.** The guard row is missing and only one value closes
  the goal, on such a variable (`eq_nat(x, x)` must be true; `eq_nat(x, y)`
  must be false under `lt(x, y)`). Naming it lets the solver pick the wrong
  value. A lemma about the guard is missing.

On a tell: add no hint for that goal; finish the other goals' candidates if
any; report the tell with the model lines that show it (§9).

## 7. No model: ledger mode

Entered only for a failing goal with no `_model.json`. The inputs are the
source and the goal's `_instantiated_terms.smt2`: its header (`lemma`, `goal`,
`branch`, the `definitions` block) and the `; instantiated terms:` groups —
the applications the query has in hand, from the goal, the hypotheses, the
patterns and the user hints. There is no value information, so nothing says
which application is stuck; the method is a frontier search over the ledger:

1. One row per application in the ledger whose scrutinee's shape the branch
   fixes: application | shape | equation → inner terms and guard | in the
   ledger?
2. Candidates = the inner terms and guards absent from every group. The
   equation's outermost result is never a candidate (the peephole).
3. Add all candidates of all such goals, re-run once, re-read. A hint now
   appears under `from the user hints:` and opens the next level.
4. Cap unfolding at two levels per function per goal; a frontier emptied only
   by that cap is *limited*, not saturated, and the report must say so.

Read the outcome of each re-run: `unsat` — done (an UNKNOWN goal may have
been true all along, and the hint made it tractable); `sat` with a model —
switch that goal to model mode; still no model — next frontier round. A
round that adds no candidate is **saturation**: report it with the last table.
The three tells of §6 cannot be read without a model; do not guess a lemma
from the ledger. Ledger mode is the expensive mode — it unfolds every listed
application, not just the failing chain — and is used only when no model
exists. Example: `examples/6-ledger-mode.md`.

## 8. Edit conventions

- `instantiate!` contents are recorded, not compiled: no `Box::new`, no
  `.clone()`, no ownership concerns inside the macro.
- Use the binder names in scope in the failing branch (`n_min`, `h`, `t`); a
  hint may reference only variables bound by that branch. Rename a `_`-prefixed
  binder (`_h2` → `h2`) when a hint needs it.
- Place hints in the failing arm, before its recursive or helper call.

## 9. Report

Green: the hints added, grouped by round and branch. A tell: the goal, the
branch, the tell's name, the two or three model rows that show it, and the
fact or case split the proof appears to need — with no edit made for it.
Ledger mode: the goals handled without a model, their verdict after each
round, and on saturation (or a cap) the last frontier table.

## 10. Examples (read 0 first; each is one model, one walk)

- `examples/0-the-walk.md` — the procedure on a ten-line Nat lemma.
- `examples/1-two-guards.md` — two guards in one branch; a hypothesis already
  valued needs nothing.
- `examples/2-inner-term-fixed-constructor.md` — junk result below a
  constructor the branch fixes.
- `examples/3-two-branches-constructor-terms.md` — two failing goals, `Nat`-
  and `Pair`-typed inner terms, one re-run.
- `examples/4-nested-rounds.md` — one level per round; when to keep going.
- `examples/5-hand-off.md` — the three stop tells on real models.
- `examples/6-ledger-mode.md` — no model: the frontier over the
  instantiated-terms file, checked against example 2.

`fixtures/MANIFEST.md` says how each example's model was produced.
