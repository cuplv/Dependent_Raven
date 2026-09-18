# Fixture manifest (raven-lemma)

Lemma-gap fixtures: proofs whose instantiate procedure has been run to
saturation and which still fail — the gap is a fact (helper lemma, case
split, or recursive call), never a missing switch. Each fixture is the
INTAKE state: hints the instantiate procedure would have added are
already in the body. To run one: copy into `test_suite/tests/`, run
`cargo test --test <name>` from `test_suite/`; artifacts land in
`test_suite/logs/`. The verified originals in `test_suite/tests/` are
the answer keys.

| Fixture | Source | Gap (signature) | Failing VC | Fix |
|---|---|---|---|---|
| `prop_04_lemma_gap.rs` | `prop_04.rs` | guard lemma | `tip_04_vc_3` | add `eq_refl` (`Lemma(eq_nat(x, x))`) + call `eq_refl(n)`; the manual guard hint then becomes redundant |
| `prop_47_lemma_gap.rs` | `prop_47.rs` | algebraic lemma | `tip_47_vc_16` | add `max_comm` (`Lemma(max(a,b) == max(b,a))`) + call `max_comm(height(*l), height(*r))`; the helper's own proof needs its two wrapped-max hints (composition); the saturation-era swapped-max hint in the target then becomes redundant |
| `prop_07_case_gap.rs` | `prop_07.rs` | case split | `tip_seven_vc_1` | wrap the `n = Z` branch body in `match m { Z => (), S(_m_prime) => () }`; no lemma, no hints (the answer key's `instantiate!(sub(m, n))` is measured redundant) |
| `prop_47_ih_gap.rs` | `prop_47.rs` | missing recursive call | `tip_47_vc_19` | add `tip_47(*r.clone())` (descent: `r ⊏ t` via `Node(l, e, r)`); the saturation-era swapped-max hint then becomes redundant |
| `prop_69_shape_gap.rs` | `prop_69.rs` | shape lemma | `tip_69_vc_4` | add `add_succ_r` (`Lemma(add(x, S(y)) == S(add(x, y)))`) + call `add_succ_r(m.clone(), *n_min.clone())`; the bare helper verifies (the answer key's internal hint is measured redundant) |
| `prop_78_chain_gap.rs` | `prop_78.rs` | conditional preservation lemma (depth chain) | `tip_78_vc_6` | add `sorted_insort` (`Lemma(implies(sorted(xs), sorted(insort(x, xs))))`, depth 1; calls the already-proven `le_neg` at depth 0) + call `sorted_insort(h.clone(), sort(*t.clone()))`; the saturation-era `insort(h, sort(t))` hint then becomes redundant |

Captured artifacts per fixture: `<prop>_counterexample.smt2` (the intake
counterexample — for prop_04 it shows the guard PRESENT in user hints
with the proof failing, the guard-signature evidence) and
`<prop>_failed_query.smt2` (the raw query, kept for reference; the skill
reads it but never probes it).

All six planned fixtures are present.
