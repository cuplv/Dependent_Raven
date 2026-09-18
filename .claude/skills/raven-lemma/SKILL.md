---
name: raven-lemma
description: Diagnose a ravencheck proof that instantiation cannot fix and
  repair it by inferring a helper lemma, a case split, or a missing
  recursive call. Use when a proof still fails after raven-instantiate has
  saturated (its report, or a frontier round finding nothing), or when a
  counterexample shows a guard with a free value / permuted endpoints /
  a shapeless blocker. Constructs and proves helpers, calls them at
  validated instances; produces a named diagnosis instead of forcing a
  fix when its budgets or envelope are hit.
---

# raven-lemma

## 1. Scope and hard constraints (the envelope)

Permitted edits — ADDITIVE, PROOF-SIDE ONLY:

- new `#[val((...) -> Lemma(...))]` helper items (spec + proof body);
- statements inside proof bodies of the TARGET and of helpers this skill
  created: helper calls, and recursive self-calls subject to the descent
  rule below;
- restructuring a proof-body branch into a `match` (a case split);
- removing things this skill added, and removing `instantiate!` lines in
  the target that this skill's fix made redundant (minimization only,
  re-verifying green after each removal).

Read-only, forever: the TARGET's `Lemma(...)` specification, every
`#[val]` function definition, datatype declarations, other tests.
Never weaken a spec, never comment out a property, never mark a test
ignored.

**Inputs and the only solver run.** Progress comes from reading three
artifacts — the trial source file, `logs/<goal>_counterexample.smt2`, and
`logs/<goal>_failed_query.smt2` — and from re-running the trial file with
`cargo test --test <file>`. That is the only solver invocation. Do NOT
probe: never append asserts to a failed query, never run z3/cvc5 by hand,
never write a scratch query. A candidate is validated by one thing only:
constructing it, calling it, and re-running the test (§4 step 4).

**No `instantiate!` by this skill.** raven-lemma never writes hints
itself. Instantiations enter only through the composed raven-instantiate
procedure (§5), and only into lemmas THIS skill generated. If the target
or a pre-existing lemma needs plain hints, that is raven-instantiate's
jurisdiction: hand sideways and say so in the report.

**Descent rule (every added self-call, target or helper).** Each
argument must be the corresponding parameter unchanged or a
pattern-bound strict subterm of it, with at least one strict. A
same-argument self-call (`f(t.clone())` inside `f`) would "prove"
anything — the tool does not check termination — and is forbidden no
matter how promising the candidate looks. Every added self-call gets a report
line: `added f(*r): r ⊏ t via Node(l, e, r)`.

**Acyclicity.** A helper may not call or restate the target, directly or
transitively. Calls to already-proven lemmas are free.

Audit: after each edit, `git diff` may contain new Lemma items and
proof-body edits, but the target's spec line and all function
definitions must appear in ZERO hunks.

## 2. The ground rule

A proven lemma is not a global axiom: its fact enters a VC only through
a CALL, which both selects the instance (the arguments) and supplies the
definedness of the instance's terms. Calling a lemma is instantiating a
fact — placement and arguments are as load-bearing as the statement.
Defining a helper without calling it changes nothing.

## 3. Artifacts and commands

Identical to raven-instantiate §3 (run from `test_suite/`, counterexample
at `logs/<lemma>_vc_<k>_counterexample.smt2`, lemma-keyed logs). One
addition: a constructed helper's failing VCs are named after the HELPER
(`max_comm_vc_6`) and get their own counterexamples — the failure moving
into the helper is normal (it is the composition trigger, §5).

## 4. Procedure

1. **Intake gate.** Establish that instantiation cannot fix the failure
   (a raven-instantiate saturation report, or run its procedure to
   saturation yourself). Frontier finds candidates -> Stop L0: hand
   back. Details: `reference/classification.md`.
2. **Classify.** Test the six signatures in cost order (missing
   recursive call -> guard -> shape -> algebraic -> preservation -> case
   split), taking the first whose evidence matches. Recipes and the
   cascade rule: `reference/classification.md`.
3. **Candidate.** Derive the statement by the signature's recipe;
   generalize MINIMALLY (same constant -> same variable).
4. **Check the candidate against the counterexample, by reading.** Before
   constructing, confirm from the file that the candidate's instance
   contradicts the countermodel: its terms are in the ledger (or are
   one-step results of pinned unfoldings), and the fact at those terms is
   incompatible with the negated goal after evaluating both sides (§4 of
   `reference/classification.md`). This is desk-checking, not probing —
   no solver runs outside `cargo test`. Two traps: the goal itself,
   generalized, always "checks" (acyclicity excludes it); two facts needed
   jointly each look insufficient alone (coverage first, then pair them).
   Budget: 2-3 constructed candidates per VC that leave the target red
   -> Stop L1. A promising candidate never overrides descent/acyclicity.
5. **Construct.** For lemma signatures: pick a template
   (`reference/helper-templates.md`), write the helper BARE, add the
   call at the instance's arguments the endpoints name, in the failing
   VC's branch. For missing-IH: the descent-checked self-call. For case
   split: wrap the branch in a match on the blocking variable (the
   variable the ledger shows as shapeless). Fragment errors:
   `reference/epr-fitting.md` (one reformulation pass, else Stop L3).
6. **Compose.** Re-run. If a HELPER VC fails, apply
   `../raven-instantiate/SKILL.md`'s procedure to it (§5). If a TARGET
   VC still fails, re-classify from the top (the cascade — fixing one
   gap can surface the next).
7. **Verify and minimize (Stop L4).** Target green -> remove each added
   lemma/call in turn (keep what re-breaks), remove target hints made
   redundant, re-verifying after each removal -> report.

## 5. Composition protocol (normative)

- A constructed helper's proof fails -> apply raven-instantiate's
  procedure TO THE HELPER's failing VC, under THAT skill's envelope:
  only `instantiate!` lines, only in the helper's failing branch.
- The composed procedure saturates and the helper still fails -> the
  helper has its own lemma gap: classify from the top; constructing a
  sub-helper consumes ONE unit of lemma depth.
- New case-split arms in the TARGET needing hints -> sideways handoff
  to raven-instantiate (target jurisdiction), noted in the report; this
  skill does not add them.
- Depth accounting: depth counts stacked UNPROVEN conjectures created
  this session. Calling an already-proven lemma costs nothing.

## 6. Stop conditions (ALL ACTIVE)

- **L0 — wrong intake.** Frontier not saturated -> hand back to
  raven-instantiate. (Criterion: `reference/classification.md`.)
- **L1 — no candidate closes the VC.** No signature's evidence matches,
  or 2-3 constructed-and-called candidates each left the target red
  (with the same countermodel shape in the regenerated counterexample)
  -> report the tried candidates (statement; helper proven or not; the
  target's failing VC after the call) and the classification evidence.
  Do not conclude "unprovable".
- **L2 — budgets.** Lemma-DEPTH limit, default 3 (a conjecture chain
  growing past three unproven levels -> stop, report the chain for
  review).
  Lemma-COUNT limit, default 4 per session (beyond it, report the plan,
  not the pile). Both are overridable by invocation keywords —
  `depth-limit N` and `lemma-limit N` (e.g. "/raven-lemma — depth-limit
  4 lemma-limit 10" for proofs beyond TIP scale, such as BST/AVL/RBT
  properties). Overrides change the numbers, never the semantics:
  budget stops report state; they NEVER conclude "unprovable". Both
  budgets count only UNPROVEN conjectures created this session —
  already-proven lemmas are free, so large lemma libraries are built by
  staged sessions rather than raised limits where possible.
- **L3 — fragment rejection.** The tool's sort-cycle/fragment error
  survives one reformulation pass -> report the attempt list.
  (Criterion and template: `reference/epr-fitting.md`.)
- **L4 — success.** Verify, minimize, report (§7).
- **L5 — envelope breach required.** Every conceivable continuation
  lives in a read-only region -> refuse and report what the evidence
  suggests WITHOUT touching it. Three faces: a possibly-wrong spec (every
  constructed candidate leaves the same countermodel standing), a possibly-buggy
  definition (the counterexample's definitions block shows the suspect
  equation), circularity pressure (the only closing fact is the goal
  itself). L5 and the descent/acyclicity rules stay active under ANY
  future experimental mode — they are correctness boundaries, not
  patience policies.

## 7. Report format

Fix report: per added lemma — statement, signature, template, call
site(s) and instance arguments, composition hints (if any), depth used;
per added self-call — the mandatory descent line; removals from
minimization; final verified state.

Diagnosis report (L0/L1/L3/L5): the named stop, the evidence (ledger
lines / endpoints / attempt list), tried candidates with verdicts, and
the suggested next action, explicitly out of scope.

## 8. Worked examples (imitate their stage structure)

1. `examples/1-guard-lemma.md` — guard signature; minimal generalization;
   a wrong candidate shown.
2. `examples/2-algebraic-lemma.md` — endpoint anti-unification; the
   goal-as-lemma trap; REAL composition (helper needed two hints).
3. `examples/3-case-split.md` — bare-variable blocker; structure instead
   of a lemma.

(The examples predate the no-probing rule: their "Pre-validate" sections
show solver probes that are NO LONGER performed. Imitate their
classification, candidate derivation, construction and composition;
skip the probes — the desk-check of step 4 replaces them.)
4. `examples/4-missing-ih.md` — the refined coverage check (instantiated
   goal, not variable mention); descent line demonstrated.
5. `examples/5-shape-lemma.md` — opaque-application blocker; candidate
   derived backwards from the blocked step.
6. `examples/6-depth-chain.md` — conditional preservation candidate;
   depth accounting; expression-valued instance arguments.

## 9. Reading order

Working path: this file + the examples. On demand:
`reference/classification.md`, `reference/helper-templates.md`,
`reference/epr-fitting.md`; shared background from the sibling skill:
`../raven-instantiate/reference/smt-encoding.md` (encoding + the two
absences), `.../theory.md` (the three facts), `.../counterexample-format.md`
and `.../proof-language.md`. `fixtures/` holds the six broken proofs with
captured counterexamples and failed queries (MANIFEST inside); the
verified originals in `test_suite/tests/` are the answer keys.
