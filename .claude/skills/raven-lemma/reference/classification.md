# Classification — naming the gap from the model

Inputs: the source, the goal's `test_suite/logs/<lemma>_vc_<k>_model.json`,
and the instantiate skill's stop line `STOP at <application or guard>: <why>`
(or a goal that is still `sat` after its hints). Read the model as the
instantiate skill does (`../../raven-instantiate/SKILL.md` §3): a row is a
defined application, an absent row an undefined one, an element with no
constructor row a tag.

Test the signatures **in this order** and take the first whose evidence
matches. Each fix is additive: a helper lemma called at one instance, a
self-call, or a `match`. A candidate is validated one way only: construct
it, call it, re-run.

| # | Signature | Evidence in the model | Fix |
|---|---|---|---|
| 1 | missing induction hypothesis | a pattern variable of the inductive sort, and the goal instantiated at it appears in **no** hypothesis (the IH rows for `t` are absent while the goal is about `Cons(h, t)`) | descent-checked self-call on it |
| 2 | guard that must hold | `STOP at guard g(args)`: `g` has no row at `args`, only one value closes the goal, and `args` are variables the branch does not fix; or `g` has a row with the wrong value after a hint named it | lemma fixing the value: `g(x, x)` or `hyp ⟹ ¬g(x, y)`, minimal generalization |
| 3a | case split | `STOP at f(…, v)` where the needed shape belongs to `v`, a **goal or pattern variable** with no constructor row | wrap the arm's body in `match v` |
| 3b | shape lemma | `STOP at f(…, g(…))` where the tag is the **result of an application** `g(…)` whose definition cannot fire | an equation giving `g(…)` a constructor form (`sub(n, Z) == n`); if one split suffices, `match g(…)` with a computed scrutinee instead |
| 4 | algebraic | two elements the goal equates differ, the chain is stuck at a tag, and nothing names the equality (`app(t, Nil) = NList!3 ≠ t`; `S(max(B, A))` vs `S(max(A, B))`) | the equation between the two endpoints, fresh variables at the disagreeing positions |
| 5 | conditional | the fact needed holds only under a hypothesis already in context: `P(a)` known and `P(f(x, a))` wanted (`sorted(insort(x, xs))`), or an equation valid under a side condition (`take(k, app(ys, zs)) == take(k, ys)` under `le(k, len ys)`) | `hyp ⟹ fact`, called at the instance; the side condition may need its own lemma |
| — | hand back | the stuck application sits inside a **hypothesis** and its inner term has no row (`len_a(xs) = Z` with `xs = ACons(_h, t)` and `len_a(t)` absent) | not a lemma: an `instantiate!` of the inner term; return the goal to the instantiate skill |

## Reading each signature

**1. Missing induction hypothesis.** Check first; it is the cheapest fix and
the one that makes the others look like lemmas. The test is presence of the
*instantiated goal* among the hypotheses, not whether the variable is
mentioned somewhere — a helper's postcondition may mention `t` without being
the IH. The self-call obeys the descent rule (SKILL.md §1); write the descent
line in the report.

**2. Guard that must hold.** The instantiate skill stops here when it sees
that naming the guard would let the solver pick the value (prop_04:
`eq_nat(n, n)`; prop_29 `vc_1`; prop_86: `eq_nat(x, y)` must be false under
`lt(x, y)`). The needed value is read off the `if`: the branch whose equation
reaches the goal. Generalize the instance minimally — the same element at two
positions becomes the same variable (`eq_nat(n, n)` → `∀x. eq_nat(x, x)`),
never one variable per occurrence.

**3a vs 3b. Shape.** Both stop at an equation that matches on a tag. Look at
*what the tag is*: a variable (`t` in `last(Cons(_h, t))`, prop_63) → split
on it, each new arm is its own goal; the result of an application
(`sub(len t, Z)` in prop_67/50, `add(m, S n)` in prop_69) → a lemma giving
that application a constructor form, derived backwards from the equation it
must fire. When the lemma would be a single case analysis with no induction,
a `match` on the computed scrutinee in the proof body is the cheaper fix.

**4. Algebraic.** Evaluate both goal sides through the rows until each is
stuck; the two stuck endpoints are the candidate's two sides. Put a fresh
variable at every position where they differ and nowhere else. The goal
itself, generalized, always "closes" the goal and is excluded by acyclicity
(SKILL.md §1); anti-unify the endpoints, not the goal.

**5. Conditional.** The signature of sorting- and length-indexed proofs. The
antecedent is the hypothesis that supports the fact at the instance
(`sorted(xs)` for `sorted(insort(x, xs))`; `le(k, len ys)` for `take_app_le`);
without it the statement is false. The antecedent may itself need a lemma to
be established at the call site (`sub_le` and `len_rev` in prop_72) — those
are further rounds, each classified from the top.

**Hand back.** A hypothesis that holds spuriously because one of its terms is
junk is an instantiation gap in disguise (prop_85 `vc_3`). Add no lemma;
report the term for the instantiate skill.

## After a fix

Re-run; the report lists every failing goal. A **helper's** goal that fails
goes to the instantiate skill first (its own hints), then, if still failing,
back here as a sub-helper (one unit of depth). A **target** goal that still
fails is classified again from the top: fixing one gap can surface the next
(a missing IH and an algebraic lemma can both be absent, and neither fix
alone turns the goal green). No signature matching, or two constructed
candidates leaving the goal red with the same model shape, is a stop
(SKILL.md §5) — report the evidence and the tried candidates; never conclude
"unprovable".
