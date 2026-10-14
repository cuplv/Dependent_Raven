# Fitting a helper into the fragment

A helper must be a prenex-universal statement (the `Lemma(…)` wrapper) with
a quantifier-free body over first-order terms, and it must not close a
cycle in the sort graph. A candidate from `classification.md` — a
generalized guard, an endpoint equation, a conditional over existing
functions — fits by construction. The moves below are for the creative
case, when the fact as first conceived mentions an inner quantifier or needs
a new function.

**Inner `exists` → a witness function.** `exists z. le(x, z) && le(y, z)`
is not writable; define the witness and state the lemma about it:
`fn max(x, y) -> Nat` with `Lemma(le(x, max(x, y)))` (and the `y` twin).

**Inner `forall` → a recursive predicate.** "every element of `xs` is ≤ k"
becomes `fn all_le(k, xs) -> bool`, structurally recursive; lemmas about the
property become lemmas about the predicate, proved by induction. This is the
`sorted` pattern the whole suite uses.

**A new function that closes a sort cycle.** With `height: Tree → Nat`, a
helper `build: Nat → Tree` adds the edge `Nat → Tree` and the tool rejects
the module before solving: `Found Sort Cycles! This breaks decidability.`
Restate the fact without the offending direction, or split the lemma so the
function is never registered.

Do not predict fragment membership; add the helper and run. A violation
fails fast and loud (the sort-cycle error, or a panic on an unsupported
form). Then: retract the helper, apply the matching move, retry **once**.
If the retry fails too, stop (SKILL.md §7) and report the fact in math
notation, each formulation tried, and the exact error each produced — the
attempt list says which direction of expressiveness the proof wanted.
