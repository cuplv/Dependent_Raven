# Example 2 — an inner term below a constructor the branch fixes (`fixtures/prop_64`)

The most common signature: the branch knows a variable's constructor, yet a
function applied to that variable is junk. The equation's inner term, one level
below, is not a term.

## Source (TIP prop_64)

```rust
fn last(xs: NList) -> Nat {
    match xs {
        NList::Nil => Nat::Z,
        NList::Cons(h, t) => match *t {
            NList::Nil => h,
            NList::Cons(h2, t2) => last(NList::Cons(h2, t2)),
        },
    }
}
fn app(x: NList, y: NList) -> NList { ... Cons(h, t) => Cons(h, app(*t, y)) }

#[val((x: Nat, xs: NList) -> Lemma(last(app(xs, NList::Cons(x, Box::new(NList::Nil)))) == x))]
fn tip_64(x: Nat, xs: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(_h, t) => match *t.clone() {
            NList::Nil => (),
            NList::Cons(_h2, _t2) => {
                tip_64(x, *t);
            }
        },
    }
}
```

`tip_64_vc_3` fails (the `Cons`/`Cons` arm).

## Model (abbreviated)

```json
"x": "Nat!3", "xs": "NList!1", "_h": "Nat!1", "t": "NList!3", "_h2": "Nat!2", "_t2": "NList!2",
"Cons": { "(Nat!1, NList!3)": "NList!1", "(Nat!2, NList!2)": "NList!3",
          "(Nat!3, Nil)": "NList!4", "(Nat!1, NList!5)": "NList!6" },
"app":  { "(NList!1, NList!4)": "NList!6", "(NList!3, NList!4)": "NList!5", "(Nil, y)": "y" ... },
"last": { "NList!4": "Nat!3", "NList!5": "Nat!3", "NList!6": "Nat!4", "Nil": "Z" }
```

Branch: `xs = Cons(_h, t)` and `t = Cons(_h2, _t2)` (the first two `Cons` rows).
`NList!4` is `Cons(x, Nil)`, the goal's singleton.

## The walk

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `app(xs, [x])` = `(NList!1, NList!4)` | yes → `NList!6` = `Cons(_h, NList!5)` | fired: `app(Cons(_h, t), y) = Cons(_h, app(t, y))` | fine |
| `app(t, [x])` = `(NList!3, NList!4)` | yes → `NList!5`, **junk** although `t = Cons(_h2, _t2)` | `app(Cons(_h2, _t2), y) = Cons(_h2, app(_t2, y))`: inner term `app(_t2, [x])` | follow |
| `app(_t2, [x])` = `(NList!2, NList!4)` | **no** | — | **candidate** |
| `last(app(xs, [x]))` = `last(NList!6)` | yes → `Nat!4` ≠ `x` | `last(Cons(_h, NList!5))` needs the shape of `NList!5` — junk, so stuck | consequence of the above |
| IH `last(app(t, [x]))` = `last(NList!5)` | yes → `Nat!3` = `x` | — | holds |

One missing row explains everything: with `app(_t2, [x])` present, `app(t, [x])`
becomes `Cons(_h2, …)`, `last` steps through it, and the induction hypothesis
finishes.

## Edit

```rust
NList::Cons(_h2, t2) => {
    instantiate!(app(t2, NList::Cons(x, NList::Nil)));
    tip_64(x, *t);
}
```

## Next round

Green. Note that the case split on `t` was already in the proof (a shape the
branch fixes); without it the same model would show `t` as the output of no
`Cons` row, which is example 5's second tell, not a hint.
