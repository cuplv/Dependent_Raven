---
name: raven-instantiate
description: Diagnose a failed ravencheck proof and find missing instantiate!
  hints by analyzing the generated counterexample file
  (logs/<goal>_counterexample.smt2). Use when a test_suite proof fails with
  "solver found counterexamples". Finds missing instantiations only; when
  instantiation cannot fix the failure, produces a named diagnosis (missing
  lemma / missing case split / missing recursive call) instead of forcing
  a fix.
---

# raven-instantiate

## 1. Scope and hard constraints

The ONLY permitted edit is adding `instantiate!(...)` lines inside the
failing branch of the failing lemma (and removing lines YOU added, during
minimization). Everything else is read-only: `Lemma(...)` specifications,
function definitions, match skeletons, recursive and helper calls, other
tests. Never weaken a spec, never comment out a property, never mark a
test ignored. If no permitted edit can succeed, the correct output is a
description of the final state, not a forced green test.

This constraint is ENFORCED, not just stated: procedure step 4 requires a
`git diff` self-audit after every edit, and any non-`instantiate!` change
must be reverted on the spot.

Adding hints is always sound (a hint is a true totality fact about the
real functions — `reference/theory.md`, Fact 1), so the risk of an edit is
never a false proof; the risk is only wasted effort and wrong diagnosis,
which the procedure and stop conditions control.

## 2. The ground rule

Functions in the encoding are PARTIAL: a defining equation fires only if
every application subterm it mentions — including the guard term of an
`if` — has a definedness switch in the counterexample's "instantiated
terms" ledger. An absent term does not make equations false; it makes them
silently vacuous. Why this is so is visible in the query text: see
`reference/smt-encoding.md`.

## 3. Artifacts and commands

- Run tests from `test_suite/`: `cargo test --test <file>` (file =
  `tests/<file>.rs`).
- A failure names its goal `<lemma>_vc_<k>` and writes
  `test_suite/logs/<lemma>_vc_<k>_counterexample.smt2`. The lemma is a
  `#[val(... -> Lemma(...))]` function in some `tests/*.rs`; the
  counterexample's `branch :` line identifies the match arm the VC belongs
  to — that arm is where hints go.
- Log files are keyed by LEMMA name, not file name: two test files sharing
  a lemma name overwrite each other's logs; the last run owns them.
- How to read the file: `reference/counterexample-format.md`.

## 4. Procedure

1. **Run and read.** Run the failing test; open the counterexample file.
   Identify lemma, VC, branch, definitions block, and the ledger.

2. **Coverage pre-check.** Every pattern variable bound in the `branch :`
   line must appear in some hypothesis group of the ledger. A variable in
   no hypothesis group signals a missing recursive call (induction
   hypothesis) on it — proof structure, not instantiation; stop and
   report (see §5).

3. **Frontier round.** Build a table with one row per application term in
   the ledger (imitate the tables in `examples/`):
   - columns: application | scrutinee(s) | shape known? | one-step result
     | absent terms;
   - a scrutinee's shape is known from the `branch :` line, from a literal
     constructor argument, OR from an equality established by an
     already-justified unfolding (a scrutinee equal to a defined
     constructor term is pinned — do not skip this third source);
   - for a pinned application, instantiate the matching equation of the
     definitions block; the one-step result terms are the equation's
     right-hand side subterms AND, for an `if` arm, the guard term;
   - candidates = result terms absent from the ledger. Prefer the
     outermost missing term (a deep hint switches all its subterms).

4. **Edit, self-audit, re-run.** Add ALL of the round's candidates as
   `instantiate!` lines in the failing branch, before the tail/recursive
   call (syntax: §6). Then AUDIT the edit before running anything:

   ```
   git diff -- test_suite/tests/<file>.rs
   ```

   Every `+` line must match `instantiate!( ... );` (whitespace aside) and
   there must be NO `-` lines except `instantiate!` lines you yourself
   added in an earlier round. If the diff shows anything else — a changed
   spec, a touched definition, a reordered statement — revert that change
   immediately before proceeding. Only after a clean audit, re-run the
   test.

5. **Loop or finish.**
   - Green: minimize — remove each added hint in turn, keep only those
     whose removal re-breaks the proof — then report the final set.
   - Still red: re-read the REGENERATED counterexample. Your hints now
     appear in the ledger (group "user hints"), which pins deeper
     scrutinees and enables the next layer of unfoldings. Repeat from
     step 3. Rounds correspond to unrolling depth: numeral-shaped goals
     legitimately take one round per literal constructor layer — steady
     new candidates are progress, not failure. Termination is governed by
     the stop conditions (§5).

## 5. Stop conditions: NONE (experimental mode)

This version deliberately has no stop conditions: keep running the
procedure loop (frontier round -> add candidates -> re-run) for as long as
you can act, even when a round finds no new candidate. If the frontier
seems empty, re-examine pinning (including the derived-equality source of
step 3) and continue; if you genuinely cannot find any further permitted
edit, describe the final state — the ledger, the last frontier table, and
what you observe about the two goal sides — WITHOUT concluding a
diagnosis, and without ever leaving the permitted-edit envelope of §1.

A designed (inactive) stop-condition scheme exists at
`reference/stop-conditions-draft.md`; do NOT apply it — the point of this
mode is to observe behavior without it.

## 6. Edit conventions (top three; rest in `reference/proof-language.md`)

- `instantiate!` contents are RECORDED, not compiled: no `Box::new`, no
  `.clone()`, no ownership concerns inside the macro.
- Use binder names in scope in the failing branch (`j_prime`, `h`, `t`);
  a hint may reference only variables bound by that branch.
- Never a bare `_` in a constructor pattern anywhere you touch — named
  `_x` binders only.

## 7. Report format

On success: the hints added (grouped by round), the minimization result,
and the verified state. When no further permitted edit is possible: the
final-state description of §5 — ledger, last frontier table, observations
about the goal sides — with no diagnosis verdict (designed report
templates live, inactive, in `reference/stop-conditions-draft.md`).

## 8. Worked examples (imitate their frontier tables exactly)

- `examples/1-wrapped-constructor.md` — one pinned unfolding, one missing
  wrapped term (the canonical case).
- `examples/2-parallel-hints.md` — sibling applications in one branch;
  a round's candidates are a set, added together.
- `examples/3-multiple-call-sites.md` — the same equation stuck at two
  call sites; joint necessity; deep hints cover subterms.
- `examples/4-guard-term.md` — the ledger looks complete but the
  `if`-guard has no switch; guard terms are candidates too.

## 9. Reading order

Working path: this file + the examples. On demand:
`reference/counterexample-format.md` (the artifact, section by section),
`reference/smt-encoding.md` (why the ground rule holds — background only;
never diagnose from the raw query), `reference/proof-language.md` (writing
legal edits), `reference/theory.md` (the three facts licensing the
procedure and its stops). `fixtures/` holds the broken proofs and captured
artifacts behind the examples, with a MANIFEST for regenerating them.
