# Example 0 — the walk, on Nats (`fixtures/demo_two_plus`)

One goal, one round, one hint. Everything the procedure does is visible here.

## Source

```rust
#[val]
#[recursive]
fn add(x: Nat, y: Nat) -> Nat {
    match x {
        Nat::Z => y,
        Nat::S(x_min) => Nat::S(Box::new(add(*x_min, y))),
    }
}

#[val((x: Nat) -> Lemma(add(Nat::S(Nat::S(Nat::Z)), x) == Nat::S(Nat::S(x))))]
fn two_plus(_x: Nat) {}
```

`two_plus_vc_1` fails: solver found counterexamples.

## Model (`two_plus_vc_1_model.json`)

```json
{
  "Nat": ["Nat!5", "Nat!1", "Nat!6", "Nat!3", "Nat!2", "Z", "Nat!4"],
  "x": "Nat!3",
  "add": {
    "(Nat!2, Nat!3)": "Nat!4",
    "(Z, Nat!5)": "Nat!5", "(Z, Nat!1)": "Nat!1", "(Z, Nat!6)": "Nat!6",
    "(Z, Nat!3)": "Nat!3", "(Z, Nat!2)": "Nat!2", "(Z, Z)": "Z", "(Z, Nat!4)": "Nat!4"
  },
  "S": { "Nat!5": "Nat!6", "Nat!1": "Nat!2", "Nat!3": "Nat!5", "Z": "Nat!1" }
}
```

## Reading it

Shapes from the `S` rows: `Nat!1 = S(Z)`, `Nat!2 = S(S(Z))`, `Nat!5 = S(x)`,
`Nat!6 = S(S(x))`. `Nat!4` is the output of no constructor row: junk.

The goal at these elements: `add(Nat!2, Nat!3) == Nat!6`. The left side has the
row `(Nat!2, Nat!3) → Nat!4`, so the model says `Nat!4 ≠ Nat!6`.

The `(Z, y) → y` rows are the equation `add(Z, y) = y`, which has no inner term
and therefore holds everywhere. They are not named terms and not hints.

## The walk

| application (elements) | row? | equation that applies, its inner terms | verdict |
|---|---|---|---|
| `add(S(S(Z)), x)` = `add(Nat!2, Nat!3)` | yes → `Nat!4`, junk | `add(S(x'), y) = S(add(x', y))` with `x' = S(Z)`: inner term `add(S(Z), x)` | follow |
| `add(S(Z), x)` = `add(Nat!1, Nat!3)` | **no** | — | **candidate** |

Arguments of the candidate are a literal and the goal variable itself; nothing
depends on an unfixed shape. Inner term → hint.

## Edit

```rust
fn two_plus(x: Nat) {
    instantiate!(add(Nat::S(Nat::Z), x));
}
```

## Next round

Green. Once `add(S(Z), x)` exists, its own equation needs `add(Z, x)`, and that
row is already there for every `x` (the universal `(Z, y) → y` rows); the chain
closes without a second round.
