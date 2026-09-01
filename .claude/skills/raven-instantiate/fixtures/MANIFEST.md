# Fixture manifest

Broken proof files and the counterexamples they produce, used as raw material
for the skill's `examples/` and for acceptance-testing the skill. Each
`*_skill_example.rs` is a copy of a verified prop from `test_suite/tests/`
with only its `instantiate!` hint(s) removed (proof structure and induction
hypotheses intact). To run one: copy it into `test_suite/tests/` and run
`cargo test --test <name>` from `test_suite/`; the counterexample lands in
`test_suite/logs/<lemma>_vc_<k>_counterexample.smt2`. Note the log file name
comes from the LEMMA name, so a fixture and its original prop overwrite each
other's logs.

| Fixture | Source prop | Removed | Failing VC | Fix (restore in the failing branch) |
|---|---|---|---|---|
| `prop_09_skill_example.rs` | `prop_09.rs` | 1 hint | `tip_nine_vc_6` | `instantiate!(Nat::S(add(j_prime, k)));` |
| `prop_08_skill_example.rs` | `prop_08.rs` | 2 hints | `tip_eight_vc_5` | `instantiate!(Nat::S(add(i_prime, j)));` and `instantiate!(Nat::S(add(i_prime, k)));` |
| `prop_list_append_skill_example.rs` | `prop_list_append.rs` | 2 hints | `app_assoc_vc_5` | `instantiate!(List::Cons(h, app(t, y)));` and `instantiate!(List::Cons(h, app(t, app(y, z))));` |
| `prop_02_skill_example.rs` | `prop_02.rs` | 1 guard hint | `tip_02_vc_19` | `instantiate!(eq_nat(n, h));` |
| `prop_23_skill_example.rs` (TRIAL — not an example) | `prop_23.rs` | 2 hints | `tip_23_vc_6` | `instantiate!(Nat::S(max(a_min, b_min)));` and `instantiate!(Nat::S(max(b_min, a_min)));` |

What each example teaches:

- **prop_09** — the canonical case: one pinned unfolding (`add(j, k)` under
  `j = S(j_prime)`) whose wrapped-constructor result is absent from the ledger.
  `prop_09_failed_query.smt2` is also captured here as the annotation source
  for `reference/smt-encoding.md`.
- **prop_08** — two parallel candidates from sibling terms in ONE branch
  (`add(i, j)` and `add(i, k)` both unfold under `i = S(i_prime)`); both must
  be added.
- **prop_list_append** — two candidates from different call sites of the same
  equation (`app(x, y)` and `app(x, app(y, z))` under `x = Cons(h, t)`);
  each alone is insufficient (minimality), and a deep hint covers its subterms.
- **prop_02** — the guard-term case: no unfolding RESULT is missing, but the
  guard `eq_nat(n, h)` of count's if-equations has no definedness switch, so
  both guarded equations are vacuous in both directions. The ledger "looks
  complete" — detection needs the guard-terms-are-candidates rule.

Fixture counterexamples were captured with the skeleton emitter (steps 0-6:
header / definitions / declarations / path asserts / ledger / negated goal).
Regenerate them after the engine lands (equalities + trace sections) so the
examples match what users actually see.

## Trial fixtures (held out of examples/ — acceptance testing only)

`prop_23_skill_example.rs` is deliberately NOT referenced by any example:
it exists to acceptance-test the skill on unseen material. Trial protocol:
start from a clean tree, copy the fixture into `test_suite/tests/`, open a
FRESH session, invoke `/raven-instantiate` with a minimal prompt naming the
failing test, and do not steer. Afterward audit with `git status` /
`git diff` (only added `instantiate!` lines may appear), record the outcome
in `trial-notes.md`, and remove the copy from `tests/`.
