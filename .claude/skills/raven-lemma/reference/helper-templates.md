# Helper-proof templates

Skeletons for constructed helpers, each taken from a verified proof in
`test_suite/tests/`. Pick by the shape of the candidate statement; fill
in the recursive calls; hints are NOT part of a template — if the bare
skeleton fails, that is the composition loop's job (see the note at the
end). Every template already satisfies the descent rule (self-calls on
pattern-bound strict subterms) and acyclicity (no calls to the target).

## T-A. Single-variable structural induction

For: properties of one inductive value — reflexivity-style guard lemmas,
`f(x, Z) == x` identities. (Verified: `eq_refl` in prop_04/24/25;
`add_zero`, `sub_zero` in prop_54.)

```rust
#[val((x: Nat) -> Lemma( P(x) ))]
fn helper(x: Nat) {
    match x {
        Nat::Z => (),                       // base: definitional
        Nat::S(x_min) => helper(*x_min),    // IH one level down
    }
}
```

## T-B. Two-variable nested induction

For: symmetric relations between two values — commutativity, totality.
(Verified: `max_comm` in prop_23/47; `le_neg` in prop_77/78; `tip_32`,
`tip_34`.)

```rust
#[val((a: Nat, b: Nat) -> Lemma( P(a, b) ))]
fn helper(a: Nat, b: Nat) {
    match a {
        Nat::Z => match b {
            Nat::Z => (),
            Nat::S(_b_min) => (),           // may need a call, e.g.
        },                                  //   eq_refl(b) in prop_25
        Nat::S(a_min) => match b {
            Nat::Z => (),
            Nat::S(b_min) => {
                helper(*a_min, *b_min);     // both strictly smaller
            }
        },
    }
}
```

## T-C. Right-argument family

For: equations whose interesting structure sits in the argument the
function does NOT recurse on — `f(x, S(y)) == S(f(x, y))`,
`f(x, Z) == x`. Induct on the argument the function DOES recurse on
(usually the first): the other side then follows the recursion.
(Verified: `add_succ_r` in prop_54/65/69/78-family; `add_one` in
prop_52.)

```rust
#[val((x: Nat, y: Nat) -> Lemma( add(x, S(y)) == S(add(x, y)) ))]
fn helper(x: Nat, y: Nat) {
    match x {                               // add recurses on x
        Nat::Z => (),
        Nat::S(x_min) => helper(*x_min, y), // y unchanged: still descent
    }
}
```

## T-D. Conditional lemma (implies)

For: preservation and gated facts — `implies(P, Q)`. Branches where the
antecedent is definitionally false close for free (the VC is vacuous);
in the inductive branch the antecedent steps down alongside the goal and
unlocks the IH's gate. (Verified: `le_neg`; `tip_70`.)

```rust
#[val((m: Nat, n: Nat) -> Lemma(implies(le(m, n), le(m, Nat::S(Box::new(n))))))]
fn helper(m: Nat, n: Nat) {
    match m {
        Nat::Z => (),                       // conclusion definitional
        Nat::S(m_min) => match n {
            Nat::Z => (),                   // antecedent false: vacuous
            Nat::S(n_min) => helper(*m_min, *n_min),
        },
    }
}
```

## T-E. List induction (with guards in the definitions)

For: properties of recursive list functions. The head case splits are
driven by the definitions' `if`-guards; supply both guard outcomes'
facts unconditionally, or split with `if` in the proof body (legal since
the T-IF checking rule; `tests/if_match_proof.rs` shows the natural
guard-then-shape structure). (Verified: `count_app` in prop_02/52;
`sorted_insort` in prop_77/78 — including a nested match on the tail to
expose its head.)

```rust
#[val((n: Nat, xs: NList, ys: NList) -> Lemma( P(n, xs, ys) ))]
fn helper(n: Nat, xs: NList, ys: NList) {
    match xs {
        NList::Nil => (),
        NList::Cons(h, t) => {
            // guard terms and wrapped results usually needed here
            // (composition supplies them); calls to proven lemmas
            // (e.g. le_neg) welcome at depth 0
            helper(n, *t, ys);
        }
    }
}
```

## Conventions that apply to every template

- **Spec boxing:** boxed constructor fields need `Box::new` in the
  `Lemma(...)` spec (it is parsed as a Rust expression); never inside
  `instantiate!`.
- **Placement:** ABOVE every lemma that calls it. Items are registered in
  file order and a call is resolved against the functions registered so
  far, so a helper placed below its caller fails with "Unbound function or
  lemma: <helper>". House style is directly above the target with a
  `// Helper:` comment stating the statement in words.
- **Patterns:** `_` inside a constructor pattern is fine; a bare `_ =>`
  arm after a constructor arm is expanded to the uncovered constructors
  (one VC each in a proof body).
- **Descent & acyclicity:** self-calls only on corresponding-parameter
  strict subterms (at least one strict); no calls to the target, ever;
  calls to already-proven lemmas are free (no depth cost).

## The composition note (applies to every template)

Templates ship BARE — no `instantiate!` lines. Run the bare helper
first: it often verifies as-is (measured: `eq_refl`, `add_succ_r`,
`tip_70`). If a helper VC fails, apply
`../../raven-instantiate/SKILL.md`'s procedure TO THE HELPER's failing
VC, under that skill's envelope (only `instantiate!` lines, only in the
helper's failing branch). Typical frontier finds, by template: T-B —
the two wrapped results of the symmetric calls
(`S(max(a_min, b_min))`, `S(max(b_min, a_min))` — measured in
example 2); T-E — guard terms (`eq_nat(n, h)`) and wrapped
results/`Cons` chains (measured in prop_02 and prop_77's history). If
the composed procedure saturates and the helper STILL fails, the helper
has its own lemma gap: one unit of the depth budget, classified from the
top (`classification.md`).
