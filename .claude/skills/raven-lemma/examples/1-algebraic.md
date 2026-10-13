# Example 1 — algebraic: the endpoints differ at a stuck tag

## A. prop_59 — `implies(ys == Nil, last(app(xs, ys)) == last(xs))`

Naive proof: induction on `xs`, IH call. Stop line:
`STOP at app(t, Nil): t is a variable the branch does not fix.`

```json
"t": "NList!1", "Cons": { "(Nat!1, NList!1)": "NList!2" },
"app": { "(NList!1, Nil)": "NList!3", "(NList!2, Nil)": "NList!4", "(Nil, y)": "y" ... }
```

IH present; no guard; a split on `t` only moves the question to `t2`, because
`app(t, Nil) = t` is not one of `app`'s equations. Endpoints `app(t, Nil) =
NList!3` vs `t = NList!1` — **algebraic**; fresh variable at the one
differing position.

```rust
#[val((xs: NList) -> Lemma(app(xs, NList::Nil) == xs))]
fn app_nil(xs: NList) { match xs { NList::Nil => (), NList::Cons(_h, t) => app_nil(*t) } }
fn tip_59(xs: NList, _ys: NList) { app_nil(xs); }   // induction no longer needed
```

Green. Report: `app_nil` — algebraic — at `xs` — depth 1.

## B. prop_53 — `count(n, xs) == count(n, sort(xs))`, with composition

`tip_53_vc_2`, `xs = Cons(_h, t)`: IH holds (`count(n, t) = count(n, sort t)
= Nat!3`); `insort(h, sort t) = NList!4` is junk because `insort` matches on
`sort(t)`, a function result with no constructor form — not a shape lemma.
Endpoints `count(n, Cons(h, t))` vs `count(n, insort(h, sort t))`: the
missing fact is how `count` sees `insort` against `Cons`.

```rust
#[val((n: Nat, x: Nat, s: NList) -> Lemma(count(n, insort(x, s)) == count(n, NList::Cons(x, s))))]
fn count_insort(n: Nat, x: Nat, s: NList) { match s { NList::Nil => (), NList::Cons(h, t) => count_insort(n, x, *t) } }
// target, Cons arm: count_insort(n, h, sort(t)); tip_53(n, t);
```

Re-run: `count_insort_vc_2` and `tip_53_vc_2` fail. §3 step 4: the
instantiate skill on the helper adds `le(x, h)`, `eq_nat(n, h)`,
`eq_nat(n, x)`, then `count(n, s)`, then `count(n, t)`; on the target,
`eq_nat(n, h)`. Green. Report: `count_insort` — algebraic — at
`(n, h, sort(t))` — five hints by composition — depth 1.
