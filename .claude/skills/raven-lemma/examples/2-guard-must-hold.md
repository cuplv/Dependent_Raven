# Example 2 — guard that must hold: naming it only lets the solver choose

prop_04, `S(count(n, xs)) == count(n, Cons(n, xs))`, empty body. Stop line:
`STOP at guard eq_nat(n, n): only one value closes, on a variable the branch does not fix.`

```json
"n": "Nat!1", "S": { "Nat!2": "Nat!3" },
"count":  { "(Nat!1, NList!0)": "Nat!2", "(Nat!1, NList!1)": "Nat!4" },
"eq_nat": { "(Z, Z)": "true" }
```

`count(n, Cons(n, xs))` is junk; its equation is `if eq_nat(n, n)
{ S(count(n, xs)) } else { count(n, xs) }`. Value `true` gives `Nat!3`, the
left side; `false` gives `Nat!2 ≠ Nat!3`. With `instantiate!(eq_nat(n, n))`
added anyway, the next model has `"(Nat!1, Nat!1)": "false"` and the goal is
still refuted: existence was never the gap, the value is.

No induction, so no IH to miss. **Guard that must hold**, value `true`;
minimal generalization keeps the two equal positions equal — `∀x.
eq_nat(x, x)`, not `∀x y`.

```rust
#[val((x: Nat) -> Lemma(eq_nat(x, x)))]
fn eq_refl(x: Nat) { match x { Nat::Z => (), Nat::S(x_min) => eq_refl(*x_min) } }
fn tip_04(n: Nat, _xs: NList) { eq_refl(n); }
```

The call asserts the value and makes `eq_nat(n, n)` a term, so the `then`
equation fires. Green. Report: `eq_refl` — guard that must hold — at `n` —
depth 1.

**Negative form** (prop_86, hypothesis `lt(x, y)`, stop at `eq_nat(x, y)`
needing `false`): the hypothesis becomes the antecedent,
`implies(lt(x, y), !eq_nat(x, y))`, induction on `y` then `x`, called at
`(x, y)`.
