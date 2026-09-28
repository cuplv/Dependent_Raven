# Example 1 — two guards in one branch (`fixtures/prop_71`)

Guards are inner terms of `if` equations. A branch may need several; a round's
candidates are added together. A guard that the model already values needs
nothing.

## Source (TIP prop_71)

```rust
fn elem(x: Nat, xs: NList) -> bool {          // Nil => false
    ... NList::Cons(h, t) => if eq_nat(x, h) { true } else { elem(x, *t) }
}
fn ins(x: Nat, xs: NList) -> NList {          // Nil => Cons(x, Nil)
    ... NList::Cons(h, t) => if lt(x, h) { Cons(x, Cons(h, t)) } else { Cons(h, ins(x, *t)) }
}

#[val((x: Nat, y: Nat, xs: NList) -> Lemma(implies(!eq_nat(x, y), elem(x, ins(y, xs)) == elem(x, xs))))]
fn tip_71(x: Nat, y: Nat, xs: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(_h, t) => {
            tip_71(x, y, *t);
        }
    }
}
```

`tip_71_vc_2` fails (the `Cons` arm).

## Model (abbreviated to the rows the walk touches)

```json
"x": "Nat!2", "y": "Nat!3", "xs": "NList!2", "_h": "Nat!1", "t": "NList!0",
"Cons":   { "(Nat!1, NList!0)": "NList!2" },
"eq_nat": { "(Nat!2, Nat!3)": "false", "(Z, Z)": "true" },
"lt":     { "(Nat!1, Z)": "false", "(Nat!3, Z)": "false", "(Nat!2, Z)": "false", "(Z, Z)": "false" },
"ins":    { "(Nat!3, NList!2)": "NList!3", "(Nat!3, NList!0)": "NList!1" },
"elem":   { "(Nat!2, NList!3)": "true", "(Nat!2, NList!2)": "false",
            "(Nat!2, NList!0)": "false", "(Nat!2, NList!1)": "false", ... }
```

Branch: `Cons: (Nat!1, NList!0) → NList!2` is `xs = Cons(_h, t)`.

## The walk

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| hypothesis `eq_nat(x, y)` = `(Nat!2, Nat!3)` | yes → `false` | — | holds; nothing to do |
| `ins(y, xs)` = `(Nat!3, NList!2)` | yes → `NList!3`, junk | `ins(y, Cons(_h, t)) = if lt(y, _h) …`: guard `lt(y, _h)` | follow |
| guard `lt(y, _h)` = `(Nat!3, Nat!1)` | **no** | — | **candidate** (guard) |
| `elem(x, xs)` = `(Nat!2, NList!2)` | yes → `false` | `elem(x, Cons(_h, t)) = if eq_nat(x, _h) …`: guard `eq_nat(x, _h)` | follow |
| guard `eq_nat(x, _h)` = `(Nat!2, Nat!1)` | **no** | — | **candidate** (guard) |
| IH `elem(x, ins(y, t))`, `elem(x, t)` | yes, both `false` | — | consistent |

Both guards are of the *must exist* kind: whichever value they take, the proof
closes — `lt` true puts `y` in front and `elem` then meets `eq_nat(x, y)`, which
the model already values `false`; `lt` false leads to the induction hypothesis;
`eq_nat(x, _h)` true makes both sides `true`.

## Edit

```rust
NList::Cons(h, t) => {
    instantiate!(lt(y, h));
    instantiate!(eq_nat(x, h));
    tip_71(x, y, *t);
}
```

## Next round

Green. Contrast prop_86, whose hypothesis is `lt(x, y)` instead: there the guard
`eq_nat(x, y)` has no row and the proof needs it *false* — a value the hypothesis
must supply, which no hint can (see example 5).
