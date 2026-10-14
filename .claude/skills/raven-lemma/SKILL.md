---
name: raven-lemma
description: Close a failed ravencheck proof end to end. This is the
  top-level skill for test_suite proofs — use it whenever a proof fails with
  "solver found counterexamples", or the user asks to prove, close or finish
  a lemma. It runs raven-instantiate first for the missing hints; when that
  skill reports STOP, it classifies the gap from the countermodel
  (test_suite/logs/<goal>_model.json) and adds what the proof lacks — a
  helper lemma called at one instance, a recursive self-call, or a case
  split. Adds proof-side terms only, never weakens a spec or edits a
  definition; stops with a named diagnosis instead of a forced fix when no
  candidate closes the goal or the edit envelope is hit.
---

# raven-lemma

## 1. Background: the two ways a proof gets stuck

Functions reach the solver as relations with their defining equations, and
nothing says an application has a value: a definition speaks only where a
witness for the application exists. A refuted goal therefore has one of two
causes. A **missing witness**: an application the proof needs has no row in
the model, so its equation never fired — repaired by `instantiate!`, the
instantiate skill's job. A **missing fact**: every application the goal
reaches is defined and the model still refutes it — no finite set of
witnesses helps; the context lacks an inductive fact or a case distinction.
That is this skill's job. Both repairs are additive and sound: they can turn
a refuted goal into a proven one, never the reverse.

## 2. How a lemma works

A lemma is a function whose spec ends in `Lemma(…)`; its body is the proof,
one goal per arm. A proven lemma is not an axiom: its fact enters another
goal only through a **call**, which fixes the instance and makes the
instance's terms defined. Defining a helper without calling it changes
nothing. Hence:

- **Placement.** The helper goes above the target (items resolve in file
  order); the call goes in the failing arm, before its recursive call, at
  the instance the model names.
- **Conditional facts.** `Lemma(implies(p, q))` can be called anywhere and
  deposits `p ⟹ q`; `Lemma(requires(p), ensures(q))` obliges the caller to
  prove `p` at the call. Prefer `implies` unless `p` is already in context.
- **A helper's own arms are goals** that must be proven like any other; the
  procedure recurses on them.

## 3. Contract

Permitted edits, all additive and proof-side: a new `#[val((…) -> Lemma(…))]`
helper with its proof body, placed above the target; a call to it (or to an
already-proven lemma) in a proof body; a recursive self-call; a `match` that
splits an arm. Read-only, forever: the target's `Lemma(…)`, every function
definition, datatypes, other tests. Never weaken a spec, comment out a
property or ignore a test. Removals only on the keyword `minimize`, after
green. Audit with `git diff` before reporting: the target's spec line, the
datatypes and the function definitions appear in zero hunks.

- **Descent.** Every added self-call's arguments are the corresponding
  parameters unchanged or pattern-bound strict subterms, at least one strict.
  A same-argument self-call would prove anything (termination is not
  checked). Report each as `added f(*r): r ⊏ t via Node(l, e, r)`.
- **Acyclicity.** A helper may not call or restate the target, directly or
  transitively. Calls to proven lemmas are free.
- **No `instantiate!` by this skill.** Hints enter only by running
  `raven-instantiate` on a helper this skill created (§5 step 5). Hints the
  target needs are that skill's job; say so in the report.

## 4. Inputs

The source `test_suite/tests/<file>.rs`; the failing goal's model
`test_suite/logs/<lemma>_vc_<k>_model.json`; and the instantiate skill's
STOP report, the stuck goal term and the application no hint can close (or
a goal still `sat` with its hints in place). Run from the repository root:
`cargo test -p test_suite --test <file>`. One run reports every failing goal;
a helper's goals are named after the helper (`app_nil_vc_2`) and appear in
the same run as the target's. Logs are keyed by lemma name.

## 5. Procedure

1. **Gate.** Run `raven-instantiate` on the file, always. DISCHARGED → done.
   Proceed only on STOP: a gap a hint can close is not a missing fact, so no
   lemma is hypothesized before instantiation has stopped.
2. **Intake.** For each goal still red: the instantiate skill's report — the
   stuck goal term and the application no hint can close — the model, and
   the source arm with its branch and hypotheses. These are the evidence;
   open the model.
3. **Classify.** `reference/classification.md`: test the signatures in order
   — missing IH → guard that must hold → case split / shape lemma →
   algebraic → conditional — and take the first whose model evidence
   matches; a spurious hypothesis is a hand-back, not a lemma.
4. **Construct and call.** Write the helper from the signature's recipe,
   generalized minimally (same element at two positions → same variable;
   never the goal itself). Prove it by induction on its inductive argument
   (`reference/helper-templates.md` for the five shapes). Call it in the
   failing arm, before the IH, at the instance the model names. For a
   missing IH: the self-call. For a case split: the `match`. Re-run.
5. **Compose.** A **helper** goal fails → run `raven-instantiate` on it
   (its envelope: hints only, in the helper's failing arm); still failing →
   the helper has its own gap: classify from the top as a sub-helper, one
   unit of depth. A **target** goal still fails → re-classify from the top;
   two gaps can coexist. Several failing goals are independent unless one
   fact explains them all.
6. **Verify.** Target green → re-run once → report (§10). No minimization
   unless asked.

## 6. Budgets

None by default. Report the depth of unproven conjectures at every round; at
depth 3 and each level beyond, pause and show the chain before continuing —
a chain that deep usually means the decomposition is wrong. `depth-limit N`
/ `lemma-limit N` in the invocation turn these into hard stops when wanted.
Two constructed candidates per goal before re-reading the model.

## 7. Stops

- **No candidate closes it**: no signature matches, or two candidates left
  the goal refuted with the same model shape → report the evidence and the
  tried statements. Never conclude "unprovable".
- **Envelope breach required**: every continuation touches a read-only
  region — a possibly wrong spec (every candidate leaves the same model),
  a possibly wrong definition (the model's table shows the suspect
  equation), circularity (only the goal itself would close it) → refuse and
  say what the evidence suggests.
- **Fragment rejection** (sort-cycle error on a helper): one reformulation
  by `reference/epr-fitting.md`, then stop.

## 8. The procedure in twenty lines

prop_59, `implies(ys == Nil, last(app(xs, ys)) == last(xs))`, proved naively
by induction on `xs` with the IH call. Instantiate skill: STOP, goal term
`last(app(xs, Nil))`, stuck at `app(t, Nil)` with `t` a variable the branch
does not fix. Model (`tip_59_vc_2`):

```json
"xs": "NList!2", "t": "NList!1", "ys": "Nil",
"Cons": { "(Nat!1, NList!1)": "NList!2" },
"app":  { "(NList!1, Nil)": "NList!3", "(NList!2, Nil)": "NList!4", "(Nil, y)": "y" ... }
```

Classify: not a missing IH (the IH on `t` is present); no guard; `t` is a
variable, but the equation `app` needs is `app(t, Nil) = t`, which no case
split supplies — the two endpoints `app(t, Nil) = NList!3` and `t = NList!1`
differ at a stuck tag: **algebraic**. Candidate: `app(xs, Nil) == xs`.

```rust
#[val((xs: NList) -> Lemma(app(xs, NList::Nil) == xs))]
fn app_nil(xs: NList) {
    match xs { NList::Nil => (), NList::Cons(_h, t) => app_nil(*t) }
}
// target: the induction is no longer needed
fn tip_59(xs: NList, _ys: NList) { app_nil(xs); }
```

Re-run: green. Report: `app_nil` — algebraic — called at `xs` — depth 1.

## 9. Writing a helper

Helper above the target; its spec in the same `Lemma(…)` syntax (`Box::new`
inside constructor literals, `implies(p, q)` for a conditional); its body
compiled Rust, so `.clone()` what is reused and `*` boxed pattern variables;
the call before the arm's recursive call. Templates: `reference/helper-templates.md`.

## 10. Report

Per helper: statement, signature, call site and instance, hints the
instantiate skill added to it, depth. Per self-call: the descent line. Per
case split: the variable. Final state: green, or the stop (§7) with its
evidence and the tried candidates.

## 11. What to open, and when

`reference/classification.md` at step 2, always. `reference/helper-templates.md`
when writing a helper; `reference/epr-fitting.md` only on a sort-cycle error.
One example when its signature is matched: `1-algebraic` (prop_59; and
prop_53, whose helper needs the instantiate skill — real composition),
`2-guard-must-hold` (includes the run where a hinted guard came back
`false`), `3-case-split`, `4-shape-lemma` (and the computed-scrutinee `match`
alternative), `5-conditional` (prop_72: a side condition that needs lemmas
of its own), `6-missing-ih` (why it is tested first). With the keyword `verbose`, read the matched
signature's example before constructing. `fixtures/MANIFEST.md` says how each
example's model was produced.
