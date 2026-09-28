# Example 4 — rounds nest one level at a time (`fixtures/prop_53`)

Each round's model shows exactly one missing level; the next round's model
shows the level below it. Keep going while each new model has a *new* absent
row on the walk.

## Source (TIP prop_53's helper, after its guards were named in an earlier round)

```rust
fn count(x: Nat, xs: NList) -> Nat {   // Nil => Z
    ... NList::Cons(h, t) => if eq_nat(x, h) { S(count(x, *t)) } else { count(x, *t) }
}
fn insort(x: Nat, xs: NList) -> NList { // Nil => Cons(x, Nil)
    ... NList::Cons(h, t) => if le(x, h) { Cons(x, Cons(h, t)) } else { Cons(h, insort(x, *t)) }
}

#[val((n: Nat, x: Nat, s: NList) -> Lemma(count(n, insort(x, s)) == count(n, NList::Cons(x, s))))]
fn count_insort(n: Nat, x: Nat, s: NList) {
    match s {
        NList::Nil => (),
        NList::Cons(h, t) => {
            instantiate!(le(x, h));
            instantiate!(eq_nat(n, h));
            instantiate!(eq_nat(n, x));
            count_insort(n, x, *t);
        }
    }
}
```

`count_insort_vc_2` still fails.

## Round A — model (abbreviated)

```json
"x": "Nat!1", "n": "Nat!3", "s": "NList!2", "t": "NList!1", "h": "Nat!2",
"Cons":   { "(Nat!2, NList!1)": "NList!2", "(Nat!1, NList!2)": "NList!6",
            "(Nat!1, NList!1)": "NList!4", "(Nat!2, NList!3)": "NList!5" },
"S":      { "Nat!4": "Nat!5" },
"le":     { "(Nat!1, Nat!2)": "false", ... },
"eq_nat": { "(Nat!3, Nat!2)": "true", "(Nat!3, Nat!1)": "true", ... },
"insort": { "(Nat!1, NList!2)": "NList!5", "(Nat!1, NList!1)": "NList!3" },
"count":  { "(Nat!3, NList!5)": "Nat!5", "(Nat!3, NList!3)": "Nat!4",
            "(Nat!3, NList!4)": "Nat!4", "(Nat!3, NList!6)": "Nat!6", ... }
```

All three guards now have rows (`le(x, h)` false, both `eq_nat` true). Shapes:
`NList!6 = Cons(x, s)`, `NList!5 = insort(x, s) = Cons(h, insort(x, t))`,
`Nat!5 = S(Nat!4)`; `Nat!6` is junk.

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `count(n, insort(x, s))` = `count(n, NList!5)` | yes → `Nat!5 = S(Nat!4)` | fired: `eq_nat(n, h)` true → `S(count(n, insort(x, t)))` | fine |
| IH `count(n, insort(x, t))`, `count(n, Cons(x, t))` | yes → `Nat!4`, `Nat!4` | | holds |
| `count(n, Cons(x, s))` = `count(n, NList!6)` | yes → `Nat!6`, **junk** | `eq_nat(n, x)` true → `S(count(n, s))`: inner `count(n, s)` | follow |
| `count(n, s)` = `(Nat!3, NList!2)` | **no** | — | **candidate** |

Edit: `instantiate!(count(n, s));` — re-run.

## Round B — model (abbreviated)

```json
"S":     { "Nat!4": "Nat!7", "Nat!5": "Nat!6" },
"count": { "(Nat!3, NList!2)": "Nat!4",      // count(n, s), now present
           "(Nat!3, NList!6)": "Nat!7",      // count(n, Cons(x, s)) = S(count(n, s))  ✓
           "(Nat!3, NList!5)": "Nat!6",      // count(n, insort(x, s)) = S(Nat!5)
           "(Nat!3, NList!3)": "Nat!5", "(Nat!3, NList!4)": "Nat!5", ... }
```

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `count(n, Cons(x, s))` | yes → `Nat!7 = S(Nat!4)` | fired | fine |
| `count(n, s)` = `count(n, Cons(h, t))` | yes → `Nat!4`, **junk** (output of no `S` row) | `eq_nat(n, h)` true → `S(count(n, t))`: inner `count(n, t)` | follow |
| `count(n, t)` = `(Nat!3, NList!1)` | **no** | — | **candidate** |
| IH's `count(n, Cons(x, t))` | yes → `Nat!5`, junk | same inner term `count(n, t)` | same candidate |

Edit: `instantiate!(count(n, t));` — re-run.

## Round C

Green. Two rounds, one level each: `Cons(x, s)` needed `count(n, s)`, and
`s = Cons(h, t)` in turn needed `count(n, t)`. The signal to stop looping is
the absence of any new absent row on the walk, not a fixed number of rounds.
