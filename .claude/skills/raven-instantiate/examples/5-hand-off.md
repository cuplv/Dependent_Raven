# Example 5 — the three tells that end the walk without a hint

Three goals from three benchmarks, each out of this skill's reach. The correct
output for each is a report naming the tell — not a hint, and not another round.
(`fixtures/prop_59`, `fixtures/prop_63`, `fixtures/prop_29`)

## A. Algebraic — `app(t, Nil) ≠ t` at a variable no branch fixes (prop_59)

```rust
#[val((xs: NList, ys: NList) -> Lemma(implies(ys == NList::Nil, last(app(xs, ys)) == last(xs))))]
fn tip_59(xs: NList, ys: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(_h, t) => { tip_59(*t, ys); }
    }
}
```

`tip_59_vc_2`, model (abbreviated):

```json
"ys": "Nil", "xs": "NList!2", "_h": "Nat!1", "t": "NList!1",
"Cons": { "(Nat!1, NList!1)": "NList!2", "(Nat!1, NList!3)": "NList!4" },
"app":  { "(NList!2, Nil)": "NList!4", "(NList!1, Nil)": "NList!3", "(Nil, y)": "y" ... },
"last": { "NList!4": "Nat!3", "NList!2": "Nat!4", "NList!3": "Nat!2", "NList!1": "Nat!2", "Nil": "Z" }
```

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `app(xs, Nil)` | yes → `NList!4 = Cons(_h, NList!3)` | fired | fine |
| `app(t, Nil)` = `(NList!1, Nil)` | yes → `NList!3`, junk | `t` is the output of **no** `Cons` row and the branch does not fix it: no equation of `app` applies | **stop** |

`t` is a tag, `app(t, Nil)` and `t` are different elements, and the equation the
goal needs — `app(t, Nil) = t` — is not a defining equation of `app` at all. No
term can be named that makes it fire. Report: *algebraic; the missing fact is
`app(t, Nil) == t` for all `t` (a lemma by induction on `t`).*

## B. Shape — a function matching on a variable that is a tag (prop_63)

```rust
#[val((n: Nat, xs: NList) -> Lemma(implies(lt(n, len(xs)), last(drop(n, xs)) == last(xs))))]
fn tip_63(n: Nat, xs: NList) {
    match n {
        Nat::Z => (),
        Nat::S(n_min) => match xs {
            NList::Nil => (),
            NList::Cons(_h, t) => { tip_63(*n_min, *t); }
        },
    }
}
```

`tip_63_vc_3`, model (abbreviated):

```json
"n": "Nat!6", "n_min": "Nat!1", "xs": "NList!2", "_h": "Nat!2", "t": "NList!1",
"S":    { "Nat!1": "Nat!6", "Nat!3": "Nat!5" },
"Cons": { "(Nat!2, NList!1)": "NList!2" },
"drop": { "(Nat!6, NList!2)": "NList!3", "(Nat!1, NList!1)": "NList!3", ... },
"last": { "NList!3": "Nat!4", "NList!2": "Nat!7", "NList!1": "Nat!4", "Nil": "Z" },
"len":  { "NList!2": "Nat!5", "NList!1": "Nat!3", "Nil": "Z" }
```

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `drop(n, xs)` | yes → `NList!3` = `drop(n', t)` | fired | fine |
| IH `last(drop(n', t)) == last(t)` | `Nat!4 = Nat!4` | | holds |
| `last(xs)` = `last(Cons(_h, t))` | yes → `Nat!7` | `last(Cons(h, t))` matches on `t`; `t` is the output of no `Cons` row and the branch does not fix it | **stop** |

The next equation needs the *shape* of `t`, and a hint can only name terms, not
give a variable a constructor. Report: *shape; the proof needs a case split on
`t` inside the `Cons` arm (for `t == Nil` the hypothesis `lt(n', Z)` is false).*

## C. Guard, must hold — the missing guard's value is dictated (prop_29)

```rust
#[val((x: Nat, xs: NList) -> Lemma(elem(x, ins1(x, xs))))]
fn tip_29(x: Nat, xs: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(_h, t) => { tip_29(x, *t); }
    }
}
```

`tip_29_vc_1` (the `Nil` arm), model:

```json
"xs": "Nil", "x": "Nat!1",
"Cons":   { "(Nat!1, Nil)": "NList!1" },
"ins1":   { "(Nat!1, Nil)": "NList!1" },
"eq_nat": { "(Z, Z)": "true" },
"elem":   { "(Nat!1, NList!1)": "false", "(Nat!1, Nil)": "false", "(Z, Nil)": "false" }
```

| application | row? | equation, inner terms | verdict |
|---|---|---|---|
| `ins1(x, Nil)` | yes → `NList!1 = Cons(x, Nil)` | fired | fine |
| `elem(x, Cons(x, Nil))` | yes → `false` | `if eq_nat(x, x) { true } else { elem(x, Nil) }`: guard `eq_nat(x, x)` | follow |
| guard `eq_nat(x, x)` = `(Nat!1, Nat!1)` | **no** | looks like a guard candidate — but only the value `true` closes the goal (`false` gives `elem(x, Nil) = false`, the model's refutation), and `x` is a tag the branch does not fix | **stop** |

Naming `eq_nat(x, x)` would give it a row, and the solver would choose `false`.
The fact needed is about the guard's *value* on an arbitrary `x`. Report: *guard
must hold; the missing fact is `eq_nat(x, x)` for all `x` (a lemma by induction
on `x`).* Compare the `Cons` arm of the same lemma, where `eq_nat(x, _h)` is a
plain guard candidate because either value closes (example 1).

## The three tells, in one line each

- **Algebraic**: the stuck application's recursion argument is a tag the branch
  does not fix, and the goal equates it with something else.
- **Shape**: the next equation matches on a variable that is a tag the branch
  does not fix.
- **Guard must hold**: the guard row is missing, and the goal or a hypothesis
  needs one specific value of it on such a variable.
