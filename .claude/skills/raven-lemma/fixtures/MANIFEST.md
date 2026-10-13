# Fixture manifest

The models behind `examples/`, verbatim as the verifier wrote them
(`test_suite/logs/<lemma>_vc_<k>_model.json`, z3 5.1.0 in process). One
directory per benchmark; the prefix says the round (`first_` = the naive
attempt, `second_` = after one fix).

To regenerate: copy the committed `test_suite/tests/<prop>.rs` to a temporary
name in the same directory, remove what the "Removed" column names (nothing
else), run `cargo test -p test_suite --test <temp>`, take the model file
from `test_suite/logs/`, delete the copy. Log files are keyed by lemma name,
so run one fixture at a time. Tag names (`Nat!4`) differ between runs; only
the rows relating them are stable.

| Fixture | Source | Removed | Failing goal | Example |
|---|---|---|---|---|
| `prop_59/first_…` | `tests/prop_59.rs` | helper `app_nil`; the main body replaced by induction on `xs` with the IH call | `tip_59_vc_2` | 1A |
| `prop_53/first_…` | `tests/prop_53.rs` | helper `count_insort` and the guard hint; main body = induction on `xs` | `tip_53_vc_2` | 1B |
| `prop_04/first_…`, `prop_04/second_guard_hinted_…` | `tests/prop_04.rs` | helper `eq_refl`; the second model has `instantiate!(eq_nat(n, n))` added instead | `tip_04_vc_1` | 2 |
| `prop_63/first_…` | `tests/prop_63.rs` | the case split on `t` | `tip_63_vc_3` | 3 |
| `prop_67/first_…` | `tests/prop_67.rs` | helper `sub_zero` | `tip_67_vc_3` | 4 |
| `prop_72/second_…` | `tests/prop_72.rs` | all helpers; main body = induction on `i`, case on `xs`, plus the one hint `app(rev(t), Cons(h, Nil))` the instantiate skill adds first | `tip_72_vc_3` | 5 |
| `prop_47/ih_gap_…` + `prop_47_ih_gap.rs` | the `.rs` in this directory (prop_47 with the IH on `r` removed) | run as is | `tip_47_vc_2` | 6 |

The full round-by-round captures live outside the skill in
`doc/skill_fixtures/`, with a README classifying every failure.
