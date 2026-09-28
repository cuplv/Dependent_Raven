# Fixture manifest

The models behind `examples/`, verbatim as the verifier wrote them
(`test_suite/logs/<lemma>_vc_<k>_model.json`, z3 5.1.0 in process). Each
directory is one benchmark; each file is one failing goal of one round. The
prefix says the round: `first_` = the attempt with no hint in that branch,
`third_`/`fourth_` = later rounds of the same goal.

To regenerate a fixture: copy the committed `test_suite/tests/<prop>.rs` to a
temporary name in the same directory, remove the hints named in the "Removed"
column (nothing else), run `cargo test -p test_suite --test <temp>`, take the
model file from `test_suite/logs/`, delete the temporary copy. Log files are
keyed by lemma name, so run one fixture at a time. Tag names (`Nat!4`) differ
between runs; only the rows relating them are stable.

| Fixture | Source | Removed | Failing goal(s) | Example |
|---|---|---|---|---|
| `demo_two_plus/` | `demo_two_plus.rs` (in this directory; not a suite file) | body empty | `two_plus_vc_1` | 0 |
| `prop_71/` | `tests/prop_71.rs` | `lt(y, h)`, `eq_nat(x, h)` | `tip_71_vc_2` | 1 |
| `prop_64/` | `tests/prop_64.rs` | `app(t2, Cons(x, Nil))` | `tip_64_vc_3` | 2, and its `_instantiated_terms.smt2` (captured under the earlier `_counterexample` name) for 6 |
| `prop_82/` | `tests/prop_82.rs` | `take_a(n_min, t)`, `Pair::P(h, h2)` | `tip_82_vc_3`, `tip_82_vc_4` | 3 |
| `prop_53/` | `tests/prop_53.rs`, helper `count_insort` | `count(n, s)` (round A), then `count(n, t)` (round B); the three guard hints kept | `count_insort_vc_2`, two rounds | 4 |
| `prop_59/` | `tests/prop_59.rs` | helper `app_nil` replaced by induction on `xs` with the IH call | `tip_59_vc_2` | 5A |
| `prop_63/` | `tests/prop_63.rs` | the case split on `t` | `tip_63_vc_3` | 5B |
| `prop_29/` | `tests/prop_29.rs` | helper `eq_refl` (and the `Cons` arm's guard hint) | `tip_29_vc_1` | 5C |

The full round-by-round captures (including counterexample ledger files and
the rounds not used by the examples) live outside the skill in
`doc/skill_fixtures/`, with their own README classifying every failure.
