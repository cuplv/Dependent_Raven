# Example 1 — guards (`fixtures/prop_71`, `fixtures/prop_30`)

Guards are inner terms of `if` equations. A branch may need several; a round's
candidates are added together. A guard that the model already values needs
nothing.

## A. Two guards in one branch (TIP prop_71)

### Source

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

### Model (abbreviated to the rows the walk touches)

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

### The walk

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

### Edit

```rust
NList::Cons(h, t) => {
    instantiate!(lt(y, h));
    instantiate!(eq_nat(x, h));
    tip_71(x, y, *t);
}
```

### Next round

Green. Contrast prop_86, whose hypothesis is `lt(x, y)` instead: there the guard
`eq_nat(x, y)` has no row and the proof needs it *false* — a value the hypothesis
must supply, which no hint can (see example 5).

## B. One guard, below a guard that already fired (TIP prop_30)

Same `elem` and `ins` as A. The guard the walk reaches sits one equation below
a guard the model already values; only the absent one is a candidate.

### Source

```rust
#[val((x: Nat) -> Lemma(eq_nat(x, x)))]
fn eq_refl(x: Nat) { match x { Nat::Z => (), Nat::S(x_min) => eq_refl(*x_min) } }

#[val((x: Nat, xs: NList) -> Lemma(elem(x, ins(x, xs))))]
fn tip_30(x: Nat, xs: NList) {
    eq_refl(x.clone());
    match xs {
        NList::Nil => (),
        NList::Cons(h, t) => {
            tip_30(x, *t);
        }
    }
}
```

`tip_30_vc_2` fails (the `Cons` arm).

### Model (abbreviated)

```json
"x": "Nat!1", "xs": "NList!3", "h": "Nat!2", "t": "NList!0",
"Cons":   { "(Nat!2, NList!0)": "NList!3", "(Nat!2, NList!1)": "NList!2", "(Nat!1, NList!3)": "NList!4" },
"lt":     { "(Nat!1, Nat!2)": "false", ... },
"eq_nat": { "(Nat!1, Nat!1)": "true", "(Z, Z)": "true" },
"ins":    { "(Nat!1, NList!3)": "NList!2", "(Nat!1, NList!0)": "NList!1" },
"elem":   { "(Nat!1, NList!2)": "false", "(Nat!1, NList!1)": "true", "(Nat!1, NList!4)": "true", ... }
```

Branch: `xs = Cons(h, t)`. `NList!1 = ins(x, t)`, `NList!2 = Cons(h, NList!1)`,
`NList!4 = Cons(x, xs)`.

### The walk

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| hypothesis `eq_nat(x, x)` = `(Nat!1, Nat!1)` | yes → `true` | — | holds |
| `ins(x, xs)` = `(Nat!1, NList!3)` | yes → `NList!2 = Cons(h, ins(x, t))` | fired: guard `lt(x, h)` has a row, `false`, so the `else` equation applies | fine |
| `elem(x, ins(x, xs))` = `(Nat!1, NList!2)` | yes → `false`, the refutation | `elem(x, Cons(h, ins(x, t))) = if eq_nat(x, h) …`: guard `eq_nat(x, h)` | follow |
| guard `eq_nat(x, h)` = `(Nat!1, Nat!2)` | **no** | — | **candidate** (guard) |
| IH `elem(x, ins(x, t))` = `(Nat!1, NList!1)` | yes → `true` | — | holds |

Either value closes: `true` makes `elem` true at once; `false` falls through to
the induction hypothesis, which the model already values `true`. The other
`ins` branch, `Cons(x, Cons(h, t))`, would meet `eq_nat(x, x)`, which `eq_refl`
supplies.

### Edit

```rust
NList::Cons(h, t) => {
    instantiate!(eq_nat(x, h));
    tip_30(x, *t);
}
```

### Next round

Green. One guard, one round. `lt(x, h)` needed no hint because its row was
already in the model.
