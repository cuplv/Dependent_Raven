# Helper-proof templates

Skeletons taken from verified proofs in `test_suite/tests/`. Pick by the
shape of the statement; fill in the self-calls. Each already satisfies
descent (self-calls on pattern-bound strict subterms) and acyclicity.
Templates ship bare: if the helper's own goal fails, the instantiate skill
runs on it (SKILL.md §3 step 4), never a hint written here.

**A. One inductive argument** — reflexivity, right identities
(`eq_refl`, `add_zero`, `sub_zero`):

```rust
#[val((x: Nat) -> Lemma( P(x) ))]
fn helper(x: Nat) {
    match x { Nat::Z => (), Nat::S(x_min) => helper(*x_min) }
}
```

**B. Two arguments, nested** — commutativity, totality (`max_comm`,
`le_neg`):

```rust
#[val((a: Nat, b: Nat) -> Lemma( P(a, b) ))]
fn helper(a: Nat, b: Nat) {
    match a {
        Nat::Z => match b { Nat::Z => (), Nat::S(_b_min) => () },   // a base arm may need a call, e.g. eq_refl(b)
        Nat::S(a_min) => match b { Nat::Z => (), Nat::S(b_min) => helper(*a_min, *b_min) },
    }
}
```

**C. The other argument carries the structure** — `f(x, S(y)) == S(f(x, y))`
(`add_succ`, `add_one`): induct on the argument `f` recurses on; the other
is unchanged in the self-call, which is still descent.

```rust
#[val((x: Nat, y: Nat) -> Lemma( add(x, Nat::S(y)) == Nat::S(add(x, y)) ))]
fn helper(x: Nat, y: Nat) {
    match x { Nat::Z => (), Nat::S(x_min) => helper(*x_min, y) }
}
```

**D. Conditional** — `implies(P, Q)` (`le_succ`, `sub_le`, `take_app_le`,
`sorted_insort`): arms where the antecedent is false close by themselves;
in the inductive arm the antecedent steps down with the goal.

```rust
#[val((m: Nat, n: Nat) -> Lemma(implies(le(m, n), le(m, Nat::S(n)))))]
fn helper(m: Nat, n: Nat) {
    match m {
        Nat::Z => (),
        Nat::S(m_min) => match n { Nat::Z => (), Nat::S(n_min) => helper(*m_min, *n_min) },
    }
}
```

**E. Lists** — properties of recursive list functions (`count_app`,
`count_insort`, `len_rev`); the Cons arm usually needs guard hints and inner
terms, supplied by composition, and may call proven lemmas.

```rust
#[val((n: Nat, xs: NList, ys: NList) -> Lemma( P(n, xs, ys) ))]
fn helper(n: Nat, xs: NList, ys: NList) {
    match xs { NList::Nil => (), NList::Cons(h, t) => helper(n, *t, ys) }
}
```

Conventions: `Box::new` around boxed constructor fields inside `Lemma(…)`
(it is parsed as Rust), never inside `instantiate!`; the helper goes above
every caller (items resolve in file order — a helper below its caller fails
with "Unbound function or lemma"); `.clone()` arguments reused later in the
arm; `*` boxed pattern variables.
