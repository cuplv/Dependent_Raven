# Example 3 — case split: the tag is a variable of the proof

prop_63, `implies(lt(n, len(xs)), last(drop(n, xs)) == last(xs))`, induction
on `n`, case split on `xs`. `tip_63_vc_3`, branch `n = S(n_min), xs = Cons(_h, t)`:
`STOP at last(Cons(_h, t)): t is a variable the branch does not fix.`

```json
"t": "NList!1", "Cons": { "(Nat!2, NList!1)": "NList!2" },
"drop": { "(Nat!6, NList!2)": "NList!3", "(Nat!1, NList!1)": "NList!3" },
"last": { "NList!3": "Nat!4", "NList!2": "Nat!7", "NList!1": "Nat!4" }
```

`drop(n, xs) = drop(n', t)` fired; the IH `last(drop(n', t)) == last(t)`
holds (`Nat!4`); `last(Cons(_h, t)) = Nat!7` is junk because `last` matches
on the tail and `t` is the output of no `Cons` row.

IH present; no guard. The tag at the matching position is `t`, **a pattern
variable of the proof** — not a function result (example 4). Nothing to
state; the proof has not looked at `t`.

```rust
NList::Cons(_h, t) => match *t.clone() {
    NList::Nil => (),                              // lt(n', len(Nil)) = false
    NList::Cons(_h2, _t2) => { tip_63(*n_min, *t); }
},
```

Two goals replace one: the `Nil` arm closes by the hypothesis being false,
the `Cons` arm by `last` firing to `last(t)` and the IH. Green. Report: case
split on `t` in the `S`/`Cons` arm — no helper — depth 0.

Same stop line on `sub(len t, Z)` with `len(t)` the tag is example 4: a
`match` on `t` would not give `len(t)` a shape. Read what the tag *is*.
