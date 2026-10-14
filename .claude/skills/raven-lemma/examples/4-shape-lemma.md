# Example 4 — shape lemma: the tag is an application's result

prop_67, `len(butlast(xs)) == sub(len(xs), S(Z))`, induction on `xs`, case
split on `t`. `tip_67_vc_3`, branch `xs = Cons(_h, t), t = Cons(_h2, _t2)`.
Instantiate skill: STOP, goal term `sub(len(xs), S(Z))`, stuck at
`sub(len(t2), Z)` with `len(t2)` an application whose shape no branch fixes.

```json
"t": "List!1", "S": { "Nat!1": "Nat!4", "Nat!3": "Nat!5", "Z": "Nat!2" },
"len": { "List!4": "Nat!5", "List!1": "Nat!3", "List!3": "Nat!1" },
"sub": { "(Nat!5, Nat!2)": "Nat!6", "(Nat!3, Nat!2)": "Nat!1", "(Nat!3, Z)": "Nat!6" }
```

Right side: `sub(S(len t), S Z) = sub(len t, Z) = Nat!6`, junk — `sub`
matches on its first argument and `len(t) = Nat!3` is the output of no `S`
row. Left side through the IH: `S(sub(len t, S Z))`. The goal is stuck at
`len(t)`.

IH present; no guard. The tag is `len(t)`, **a function result** — a split
on `t` would only move it to `len(t2)` (example 3). **Shape lemma**: which
form must `sub(x, Z)` take for its equation to fire? `sub(x, Z) == x`.

```rust
#[val((n: Nat) -> Lemma(sub(n, Nat::Z) == n))]
fn sub_zero(n: Nat) { match n { Nat::Z => (), Nat::S(_n_min) => () } }
// target, Cons/Cons arm: sub_zero(len(*t2)); tip_67(*t);
```

The instance is `len(t2)`: with `len(t) = S(len t2)` both sides become
`S(sub(len t2, Z))` vs `S(len t2)`. Green. Report: `sub_zero` — shape lemma —
at `len(t2)` — depth 1.

**Cheaper when one split suffices** — a `match` on the application itself
(prop_19, `Z` arm): `match len(xs) { Nat::Z => (), Nat::S(_k) => () }`. Each
arm gives `len(xs)` a constructor and `sub(len xs, Z)` fires; no helper.
Prefer the lemma when the fact is needed at several instances or inside a
helper.
