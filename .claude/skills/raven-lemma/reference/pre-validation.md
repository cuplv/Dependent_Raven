# Pre-validation: probe a candidate before proving it

A candidate lemma is worth a proof only if its facts would actually
close the failing VC. That is checkable in seconds, before any
construction: assert the candidate's GROUND INSTANCE (at the failing
VC's own terms) onto the failed query and re-check.

```
unsat  ->  the fact contradicts every surviving countermodel: it closes
           the VC. Proceed to Construct.
sat    ->  the countermodel survives the fact: even if the candidate is
           TRUE, it cannot close this VC. Reject; next candidate.
```

The principle behind the verdicts: **a useful lemma must contradict the
countermodel.** A fact the countermodel already satisfies (e.g. probing
`count(n, Cons(n, xs)) == count(n, xs)` on example 1's query — `sat`,
because that IS the countermodel's else-branch collapse) is dead weight
regardless of its truth.

## Writing the probe

Base: `logs/<lemma>_vc_<k>_failed_query.smt2` with its final
`(check-sat)` removed. Append witness declarations for the instance's
terms — one witness constant per application node, dependency-ordered
(inner first) — then the instance's assertion, then `(check-sat)`.

Name mapping (details: `../../raven-instantiate/reference/smt-encoding.md`):
function `f` -> relation `f_rel(args..., out)`; constructor `Nat::S` ->
`Nat__S_rel`; sort `T` -> `UI_T`; lemma parameters and pattern binders
keep their source names (`n`, `t`, `n_min`) — which is what makes probes
writable at all.

Real probes from the examples:

**Equality candidate** (example 2: `max(a,b) == max(b,a)` at
`(height(l), height(r))`):

```smt2
(declare-const hl UI_Nat)   (assert (height_rel l hl))
(declare-const hr UI_Nat)   (assert (height_rel r hr))
(declare-const m1 UI_Nat)   (assert (max_rel hl hr m1))
(declare-const m2 UI_Nat)   (assert (max_rel hr hl m2))
(assert (= m1 m2))
(check-sat)      ; unsat -> validated
```

**Bool-value candidate** (example 1: `eq_nat(n, n) == true`):

```smt2
(declare-const b Bool)
(assert (eq_nat_rel n n b))
(assert (= b true))
(check-sat)      ; unsat -> validated
```

**Conditional candidate** (example 6: `implies(sorted(a), sorted(insort(x, a)))`).
Preservation candidates arise precisely because the antecedent is
already a context hypothesis — so probe the CONSEQUENT alone:

```smt2
(declare-const st UI_NList)   (assert (sort_rel t st))
(declare-const iw UI_NList)   (assert (insort_rel h st iw))
(declare-const sv Bool)       (assert (sorted_rel iw sv))
(assert (= sv true))
(check-sat)      ; unsat -> validated
```

**Shape probe** (signature 6 — not a lemma instance but the same
mechanism, one probe per constructor; example 3):

```smt2
(assert (= m Nat__Z))                              ; probe 1  -> unsat
---
(declare-const m_prime UI_Nat)
(assert (Nat__S_rel m_prime m))                    ; probe 2  -> unsat
```

The split is validated only if EVERY shape probes unsat.

## Necessary, not sufficient — two known traps

1. **The goal as its own "lemma"** always probes `unsat` (its instance
   is the negated goal's complement). The acyclicity rule rejects it —
   a helper may not restate or call the target. Never let a clean probe
   overrule that rule.
2. **Conjunction gaps.** Two jointly-needed facts each probe `sat`
   alone (measured: prop_47 with both the right IH and max_comm
   missing). Mitigation is the classification ORDER: the coverage check
   (signature 1) runs first and costs no probe; fixing it first is what
   lets the remaining candidate validate. If single-candidate probes
   exhaust anyway, the L1 report's "each alone: sat" pattern is itself
   the conjunction-gap clue.

## Stop L1 — no validated candidate

**Criterion.** The recipe's candidate AND one reformulation attempt per
applicable signature — a budget of 2–3 probes total — have all returned
`sat`.

**Response.** Stop. Report every tried candidate with its verdict and
the classification evidence, e.g.:

```
No validated candidate for tip_XX_vc_k.
  tried: forall x. p(x, x)              -> sat (countermodel satisfies it)
  tried: forall x,y. q(x,y) == q(y,x)   -> sat
  evidence: guard (p a b) present with value false; endpoints ...
```

Do not force a fix; do not widen the search unboundedly. The report is
diagnostic material for the human — the tried-and-failed list plus the
evidence usually points at either a conjunction gap, a wrong
classification, or (see SKILL.md, Stop L5) a spec/definition problem
outside this skill's envelope. The trigger is purely mechanical (the
solver's answers), so L1 can never misfire on judgment.
