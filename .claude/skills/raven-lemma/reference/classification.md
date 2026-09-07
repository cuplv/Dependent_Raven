# Intake and classification

How a failing VC is admitted to this skill, and how its gap is named.
The six signatures below are ordered by cost of the fix — test them in
this order and take the first that matches. Each signature's evidence is
readable off the counterexample file; each has a worked example.

## The intake gate (Stop L0)

This skill's premise is that instantiation CANNOT fix the failure. Verify
it before anything else:

1. If a raven-instantiate report accompanies the failure (saturated,
   still failing), the premise is established — proceed.
2. Otherwise run `../../raven-instantiate/SKILL.md`'s procedure yourself,
   to saturation. If a frontier round finds candidates, you are in the
   wrong skill: **hand back** (Stop L0) — add nothing, report "frontier
   not saturated; run raven-instantiate first."

Only a saturated-and-still-failing state admits a lemma diagnosis. Why
this gate is sound: `../../raven-instantiate/reference/theory.md`, Fact 3.

## Signature 1 — Missing recursive call (cheapest; check first)

**Evidence.** For each branch-bound variable whose sort matches a lemma
parameter, ask whether the GOAL INSTANTIATED AT THAT VARIABLE appears
among the hypothesis facts. `goal[t := l]` present but `goal[t := r]`
absent → missing recursive call on `r`.

**The trap:** do NOT test "is the variable mentioned by some
hypothesis?" — an unrelated fact (e.g. a helper's postcondition) may
mention it. The test is presence of the INSTANTIATED GOAL itself.
(Example 4's fixture defeats the naive check on purpose.)

**Fix.** One self-call on the uncovered variable — subject to the
descent rule (see SKILL.md): every argument the corresponding parameter
unchanged or a pattern-bound strict subterm, at least one strict.
Mandatory report line with the justification.

**Example:** `examples/4-missing-ih.md`.

## Signature 2 — Guard lemma

**Evidence.** A guard term (the condition of an `if` in some definition)
is PRESENT in the ledger and the proof still fails: the countermodel is
choosing the guard's value freely, and no fact pins it.

**Candidate recipe.** Determine which value the proof needs (which
branch's equation must fire to bridge the goal); the candidate is the
guard instance at that value, generalized MINIMALLY — same constant to
same variable (`eq_nat(n, n)` → `forall x. eq_nat(x, x)`; never
per-occurrence, which over-generalizes to falsehood).

**Example:** `examples/1-guard-lemma.md`.

## Signature 3 — Shape lemma

**Evidence.** The goal's own step is blocked by an application in
scrutinee position that is an OPAQUE APPLICATION (`add(m, n)`) — not a
bare input variable — and the frontier is empty.

**Candidate recipe — backwards from the blocked step.** Ask which
constructor form the opaque application must take for the blocked
equation to fire AND land on an available hypothesis; the needed
instance falls out (`add(m, S(n_min)) == S(add(m, n_min))`), then
generalize minimally.

**If the recipe stalls** (no single constructor form suffices — e.g. the
application's head depends on a comparison), fall through to Signature 5.

**Example:** `examples/5-shape-lemma.md`.

## Signature 4 — Algebraic lemma (argument permutation)

**Evidence.** An equality goal whose two sides, evaluated through the
ledger's facts (unfoldings + hypotheses), reach endpoints identical up
to a permutation/regrouping of one function's arguments
(`S(max(A, B))` vs `S(max(B, A))`).

**Candidate recipe — endpoint anti-unification.** Fresh variables at the
disagreement positions: `max(a, b) == max(b, a)`.

**Rejected non-candidate:** the goal itself, generalized. Its instance
always probes `unsat` (it IS the negated goal's complement) — validation
success is necessary, not sufficient; the acyclicity rule excludes it.

**Example:** `examples/2-algebraic-lemma.md`.

## Signature 5 — Conditional preservation lemma

**Evidence.** A Bool goal atom of the form `P(f(x, A))` with the
hypothesis atom `P(A)` in context — the property is known of a term, and
the goal asks it of the term pushed through a function.

**Candidate recipe — atom anti-unification, conditionally.** Relate the
goal atom to the nearest hypothesis atom; the hypothesis becomes the
antecedent (it is the candidate's only support):
`forall x, a. implies(P(a), P(f(x, a)))`.

**Example:** `examples/6-depth-chain.md` (also demonstrates lemma-depth
accounting: the new conjecture costs one depth unit; calling
already-proven lemmas costs none).

## Signature 6 — Case split

**Evidence.** Frontier empty AND the blocking scrutinee is a BARE INPUT
VARIABLE of the lemma (contrast Signature 3's opaque application). The
ledger is typically tiny.

**Fix — structure, not a lemma.** Wrap the failing branch's body in a
match on the shapeless variable. Pre-validation is the SHAPE PROBE:
assert each constructor shape on the failed query; the split is
validated only if EVERY shape closes the VC. Each new arm is its own VC
(and may need the instantiate procedure).

**Example:** `examples/3-case-split.md`.

## The cascade rule

Signatures are not mutually exclusive states of the world; they are
tests in a decision order, and recipes may hand off:

- test in the order 1 -> 2 -> 3 -> 4 -> 5 -> 6 (cost order, with 3's
  stall falling through to 5);
- fixing one gap can surface the next (example 4's history: with BOTH
  the recursive call and the algebraic lemma missing, each candidate
  alone probes `sat`; fixing the coverage gap first is what lets the
  algebraic candidate validate) — after each fix, re-run and re-classify
  from the top;
- if no signature matches and no candidate validates within budget, that
  is Stop L1 (see `pre-validation.md`) — report the evidence and the
  tried candidates; do not force a fix.

## Summary table

| # | Signature | Evidence in the file | Fix | Example |
|---|---|---|---|---|
| 1 | missing recursive call | `goal[param := var]` absent from hypotheses | descent-checked self-call | 4 |
| 2 | guard lemma | guard term present, proof failing | guard-value lemma, minimal generalization | 1 |
| 3 | shape lemma | opaque application blocks the goal's step | constructor-form equation, derived backwards | 5 |
| 4 | algebraic lemma | endpoints differ by argument permutation | endpoint anti-unification | 2 |
| 5 | conditional preservation | `P(f(x, A))` wanted, `P(A)` known | `implies(P(a), P(f(x, a)))` | 6 |
| 6 | case split | frontier empty, bare-variable scrutinee | match on the variable; shape-probe validates | 3 |
