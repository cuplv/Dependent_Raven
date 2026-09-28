# Example 3 — two failing branches, constructor-typed inner terms (`fixtures/prop_82`)

Each failing goal is walked on its own model; all edits go in before one re-run.
Inner terms can be of any sort — here a `Nat`-counted `take` and a `Pair`
constructor whose whole table is absent.

## Source (TIP prop_82)

```rust
fn zip(xs: AList, ys: BList) -> PList {
    match xs {
        AList::ANil => PList::PNil,
        AList::ACons(h, t) => match ys {
            BList::BNil => PList::PNil,
            BList::BCons(h2, t2) => PList::PCons(Pair::P(h, h2), Box::new(zip(*t, *t2))),
        },
    }
}
// take_a, take_b, take_p: take(Z, _) = Nil; take(S n', Cons(h, t)) = Cons(h, take(n', t))

#[val((n: Nat, xs: AList, ys: BList) -> Lemma(take_p(n, zip(xs, ys)) == zip(take_a(n, xs), take_b(n, ys))))]
fn tip_82(n: Nat, xs: AList, ys: BList) {
    match n {
        Nat::Z => (),
        Nat::S(n_min) => match xs {
            AList::ANil => (),
            AList::ACons(h, t) => match ys {
                BList::BNil => (),
                BList::BCons(_h2, t2) => {
                    tip_82(*n_min, *t, *t2);
                }
            },
        },
    }
}
```

`tip_82_vc_3` (`ys = BNil`) and `tip_82_vc_4` (`ys = BCons`) fail.

## Goal 3 — model (abbreviated)

```json
"n": "Nat!1", "n_min": "Nat!0", "xs": "AList!1", "h": "A!0", "t": "AList!0", "ys": "BNil",
"S": { "Nat!0": "Nat!1" },  "ACons": { "(A!0, AList!0)": "AList!1" },
"take_a": { "(Nat!1, AList!1)": "AList!2", "(Nat!1, ANil)": "ANil", "(Z, _)": "ANil" ... },
"take_b": { "(Nat!1, BNil)": "BNil", ... },
"zip":    { "(AList!1, BNil)": "PNil", "(AList!2, BNil)": "PList!1", "(ANil, BNil)": "PNil" },
"take_p": { "(Nat!1, PNil)": "PNil", ... }
```

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `zip(xs, BNil)` | yes → `PNil` | `zip(ACons, BNil) = PNil`, no inner term | fine |
| `take_p(n, PNil)` | yes → `PNil` | | fine (left side is `PNil`) |
| `take_b(n, BNil)` | yes → `BNil` | | fine |
| `take_a(n, xs)` = `(Nat!1, AList!1)` | yes → `AList!2`, **junk** though `n = S(n')`, `xs = ACons(h, t)` | `take_a(S n', ACons(h, t)) = ACons(h, take_a(n', t))`: inner `take_a(n', t)` | follow |
| `take_a(n', t)` = `(Nat!0, AList!0)` | **no** | — | **candidate** |
| `zip(AList!2, BNil)` | yes → `PList!1` ≠ `PNil` | stuck on the junk argument | consequence |

## Goal 4 — model (abbreviated)

```json
"n": "Nat!1", "n_min": "Nat!0", "xs": "AList!1", "h": "A!0", "t": "AList!0",
"ys": "BList!1", "_h2": "B!0", "t2": "BList!0",
"ACons": { "(A!0, AList!0)": "AList!1", "(A!0, AList!2)": "AList!3" },
"BCons": { "(B!0, BList!0)": "BList!1", "(B!0, BList!2)": "BList!3" },
"zip":    { "(AList!1, BList!1)": "PList!2", "(AList!0, BList!0)": "PList!0",
            "(AList!3, BList!3)": "PList!4", "(AList!2, BList!2)": "PList!1", ... },
"take_a": { "(Nat!1, AList!1)": "AList!3", "(Nat!0, AList!0)": "AList!2", ... },
"take_p": { "(Nat!1, PList!2)": "PList!3", "(Nat!0, PList!0)": "PList!1", ... }
```

There is no `P` table and no `PCons` table: no pair and no pair-list was ever
built.

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `zip(xs, ys)` = `(AList!1, BList!1)` | yes → `PList!2`, **junk** though both are `Cons` | `zip(ACons(h,t), BCons(h2,t2)) = PCons(P(h, h2), zip(t, t2))`: inner `P(h, h2)`, `zip(t, t2)` | follow |
| `P(h, _h2)` = `P(A!0, B!0)` | **no** (no `P` table) | — | **candidate** |
| `zip(t, t2)` = `(AList!0, BList!0)` | yes → `PList!0` (the IH's term) | | fine |
| `take_a(n, xs)`, `take_b(n, ys)` | yes → `AList!3` = `ACons(h, AList!2)`, `BList!3` = `BCons(_h2, BList!2)` | fired (the IH names `take_a(n', t)`, `take_b(n', t2)`) | fine |
| `zip(AList!3, BList!3)` | yes → `PList!4`, junk | same equation, same inner term `P(h, _h2)` | same candidate |

## Edit (both branches, one pass)

```rust
BList::BNil => {
    instantiate!(take_a(n_min, t));
}
BList::BCons(h2, t2) => {
    instantiate!(Pair::P(h, h2));
    tip_82(*n_min, *t, *t2);
}
```

## Next round

Green, both goals. A constructor application (`P(h, h2)`) is an inner term
like any other: `instantiate!` accepts it.
