# Theory in three facts (CEGQI, distilled)

The tool implements counterexample-guided quantifier instantiation (CEGQI)
over a decidable fragment (EPR): every VC's sat/unsat answer is definitive
— `sat` is a real countermodel, never a solver timeout or "unknown". Three
consequences of the theory bear directly on this skill's decisions; they
are all you need.

## Fact 1 — An instantiation is a pointwise totality instance

The functions are total in reality, but the encoding carries NO totality
axiom (see `smt-encoding.md`). `instantiate!(t)` asserts, for each
application node inside `t`, exactly the totality instance at that point:
`∃r. f_rel(args, r)`. Consequences the skill uses:

- adding a hint is ALWAYS sound — it is a true statement about the real
  functions, so it can never cause a false verification;
- one deep hint covers its subterms (one instance per application node in
  the chain);
- `if`-guard terms need instances like any other application — a guard
  without one disables both of its equations.

## Fact 2 — The frontier loop is an algorithm, not a heuristic

CEGQI's refinement theorems (completeness of iterative instantiation) give:
if the goal is provable with SOME finite set of instantiations, then
iteratively adding the terms that the blocked one-step unfoldings mention
reaches a sufficient set. This is why the procedure's loop — frontier
round, add candidates, re-run, repeat on the regenerated file — terminates
with a proof whenever a proof by instantiation exists at all. The round
bound in SKILL.md is a practicality, not a soundness limit.

## Fact 3 — The stop condition is sound

When a frontier round produces no new candidate (saturation) and the query
is STILL sat, no instantiation set whatsoever can close this VC: the
countermodel lives on values the defining equations cannot reach (junk or
shapeless elements — `smt-encoding.md`, "the two deliberate absences").
The gap is then a FACT the context lacks — a missing lemma (guard value,
algebraic identity) or a missing case split — which instantiation cannot
express. Declining and reporting the named diagnosis is the theoretically
correct move, not a give-up.

## Pointer

The full development (the extended-EPR fragment, the relational-abstraction
semantics, and the refinement-completeness theorems) is in the project's
CEGQI / Lambda-EPR papers; in-repo discussions with worked experiments are
in `doc/counterexample_walkthrough.md` (mechanism B, frontier, saturation)
and `doc/code_review_analysis.md`.
