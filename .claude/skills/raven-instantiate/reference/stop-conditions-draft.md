# Stop conditions — DRAFT, deliberately NOT active

Status: designed but intentionally disabled. The current SKILL.md runs the
procedure with NO stop conditions, as an experiment: we want to observe
what happens when the skill is invoked on properties whose real gap is a
missing lemma or case split — does it keep producing candidates, does the
frontier dry up, what does it do after that. Do not apply the rules below
while this experiment is running. When the experiment concludes, this file
becomes SKILL.md §5.

## The four stops (designed)

**Stop 0 — coverage (before any frontier work).** A pattern variable bound
in the `branch :` line that appears in NO hypothesis group of the ledger
signals a missing recursive call (induction hypothesis) on that variable —
proof structure, not instantiation. Report "branch binds `<var>` but no
hypothesis mentions it — likely missing recursive call" and stop.

**Stop 1 — saturation (the ONLY gate to a missing-lemma diagnosis).**
A frontier round produces zero new candidates and the proof still fails.
Mandatory pre-saturation checklist: before declaring the frontier empty,
re-test every skipped application against equalities established by
already-justified unfoldings — a scrutinee equal to a defined constructor
term IS pinned (the third pinning source; forgetting it is the classic
false-saturation error). Only after that check, classify by signature and
report the named diagnosis with its evidence:

- a guard term PRESENT in the ledger, proof still failing
  -> missing guard lemma (a fact about the guard: reflexivity, totality);
- both goal sides fully unfolded, endpoints differing only by an argument
  permutation/regrouping -> missing algebraic lemma;
- frontier empty and the goal stuck on an application whose scrutinee is a
  bare input variable -> missing case split on that variable.

Soundness of this stop: when the frontier is saturated and the query is
still sat, no instantiation set whatsoever can close the VC
(`theory.md`, Fact 3) — declining is correct, not a give-up.

Caveat for user-imposed limits: if an `unroll-limit` (per-function;
SKILL.md §5) is active, Stop 1 requires the frontier to be empty even
IGNORING frozen functions. A frontier emptied only by the limit is LIMITED
saturation and licenses no missing-lemma diagnosis — report the capped
state instead.

**Stop 2 — progress rule (not a fixed round budget).** Continue while each
round adds at least one candidate never previously added. Rounds are
naturally bounded by the constructor depth visible in the goal, hints, and
derived unfoldings (numeral-shaped goals take one round per literal layer —
that is progress). A hard cap of 10 rounds exists ONLY as a guard against
procedural error (e.g. mis-reading the ledger and re-proposing existing
terms); hitting the cap means "report accumulated state and ask" — it is
NEVER grounds for a missing-lemma diagnosis, which Stop 1 alone licenses.

**Stop 3 — success.** The proof verifies: minimize (remove each added hint
in turn; keep only those whose removal re-breaks the proof), confirm
green, report the final hint set and which round produced each.

## Report templates (designed, also inactive)

Fix report: lemma + VC; hints added, grouped by round; minimization result
(kept / dropped); final verified state.

Diagnosis report: verdict name (missing guard lemma / missing algebraic
lemma / missing case split / missing recursive call); the evidence (the
ledger lines, endpoint pair, or uncovered branch variable); the suggested
next action, explicitly marked out of scope for this skill.
