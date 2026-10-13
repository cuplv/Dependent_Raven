# Example 5 — conditional: the fact holds only under a side condition

prop_72, `rev(drop(i, xs)) == take(sub(len(xs), i), rev(xs))`, induction on
`i`, case split on `xs`. `tip_72_vc_3`, branch `i = S(i_min), xs = Cons(h, t)`,
after the instantiate skill's one hint (`app(rev(t), Cons(h, Nil))`):
`STOP at take(sub(len(t), i_min), app(rev(t), Cons(h, Nil))): sub(len(t), i_min) is an application whose shape no branch fixes.`

```json
"t": "List!1", "i_min": "Nat!1",
"len": { "List!1": "Nat!3" }, "sub": { "(Nat!3, Nat!1)": "Nat!4" },
"rev": { "List!1": "List!2", "List!6": "List!5" }, "app": { "(List!2, List!3)": "List!7" },
"take": { "(Nat!4, List!2)": "List!5", "(Nat!4, List!7)": "List!8" }
```

IH holds: `rev(drop(i', t)) = List!5 = take(k, rev t)` with `k = sub(len t,
i') = Nat!4`. Right side `take(k, app(rev t, [h])) = List!8`. The goal is
`take(k, rev t) == take(k, app(rev t, [h]))`, stuck at the tag `k`.

IH present; no guard; `k` is a function result, but no constructor form of
`sub(len t, i')` exists (it depends on `i'`) — not a shape lemma. The
unconditional `take(k, app(ys, zs)) == take(k, ys)` is **false** for
`k > len ys`. **Conditional**: it holds under `le(k, len ys)`.

```rust
#[val((k: Nat, ys: List, zs: List) -> Lemma(implies(le(k, len(ys)), take(k, app(ys, zs)) == take(k, ys))))]
fn take_app_le(k: Nat, ys: List, zs: List) {
    match k { Nat::Z => (), Nat::S(k_min) => match ys {
        List::Nil => (), List::Cons(_h, t) => take_app_le(*k_min, *t, zs) } }
}
// target: take_app_le(sub(len(t), i_min), rev(t), List::Cons(h, Nil));
```

Re-run: still red — the antecedent `le(sub(len t, i'), len(rev t))` is not
established. Re-classify: two algebraic facts, `sub_le: le(sub(n, m), n)`
(needing `le_refl`, `le_succ`) and `len_rev: len(rev xs) == len xs` (needing
`len_app_one`), each one round. Final arm: `sub_le(len(t), i_min);
len_rev(t); take_app_le(…); tip_72(*i_min, *t);`. Green (the `Z` arm needs
`sub_zero`, `len_rev`, `take_len` the same way). Report: `take_app_le` —
conditional — depth 1; the antecedent's helpers — algebraic — each proven
before the next, so unproven depth stays at 1.
