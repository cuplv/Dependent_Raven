# The proof language: writing legal, meaningful edits

This skill edits proof files; this is the contract for edits that parse,
compile, and mean what you intend. The tool presents an F*-style interface
on Rust: refinement/`Lemma` specifications attached to functions, proof
bodies as scripts, and `instantiate!` playing the role of F*'s quantifier
-instantiation hints. Specs state WHAT; proof bodies state HOW.

## 1. Module anatomy

```rust
#[ravencheck::module]
mod tip_benchmarks {
    #[define]                      // inductive datatype (Box for recursive fields)
    pub enum Nat { Z, S(Box<Nat>) }

    #[val] #[recursive]            // a function the verifier knows definitionally
    fn add(x: Nat, y: Nat) -> Nat { ... }

    #[declare]                     // uninterpreted: signature only, no body
    type Elem = u32;

    #[val((i: Nat, j: Nat) -> Lemma(...))]   // a lemma: spec on a
    fn my_lemma(i: Nat, j: Nat) { ... }      // UNIT-returning fn whose
}                                            // body is the proof script
```

A lemma's body is a proof script, not a definition — it generates VCs, not
axioms.

## 2. Spec syntax (inside `Lemma(...)`)

- Equality goal: `Lemma(sub(add(m, n), n) == m)`
- Bare-predicate goal: `Lemma(eq_nat(x, x))`
- Implication goal: `Lemma(implies(le(m, n), le(m, Nat::S(Box::new(n)))))`
  — `implies(p, q)` (Rust has no `==>`); it nests.
- Precondition form: `Lemma(requires(le(m, n)), ensures(...))` — the
  precondition becomes the LAST argument's refinement. Equivalent for the
  lemma's own proof, but different at CALL sites: a requires-lemma
  obliges every caller to prove the precondition there (its fact then
  enters ungated), while an implies-lemma may be called unconditionally
  (its fact enters gated). The unconditional-call pattern (supplying
  both guard outcomes' facts) needs the implies form.
- Boxing: spec text must parse as a Rust expression, so boxed constructor
  fields need `Box::new` in specs: `Nat::S(Box::new(add(i, m)))`. The
  parser strips the Box.

## 3. Proof-body vocabulary (what each statement means to the verifier)

```rust
fn tip_nine(i: Nat, j: Nat, k: Nat) {
    match i {                                  // induction / case skeleton:
        Nat::Z => (),                          //   each arm = its own VC, the
        Nat::S(i_prime) => match j {           //   pattern = that VC's path
            Nat::Z => (),                      //   condition ("branch:" line)
            Nat::S(j_prime) => {
                instantiate!(Nat::S(add(j_prime, k)));  // definedness switch
                tip_nine(*i_prime, *j_prime, k);        // recursive self-call =
            }                                           // induction hypothesis
        },
    }
}
```

- `match` — the induction/case-analysis skeleton. Each arm becomes one VC;
  the arm's pattern bindings are its path conditions, shown as the
  `branch :` line of the counterexample.
- recursive self-call — the induction hypothesis: its instantiated
  postcondition enters the VC's context (a hypothesis group in the ledger).
- helper-lemma call (`eq_refl(b)`, `add_succ_r(m.clone(), *n_min.clone())`)
  — same mechanism: any proven fact into context. Arguments may be
  arbitrary expressions (`add_one(count(n.clone(), *t.clone()))`).
- `instantiate!(term)` — a definedness switch for `term` and (via its
  chain) every application subterm. Nothing else: it asserts no value.
- `()` as a branch body — "definitional from here": the VC must close from
  path conditions + accumulated facts + switches alone.
- Statement order among facts does not matter to the solver; house style is
  hints first, then calls, tail last.

## 4. `instantiate!` syntax facts

The contents are RECORDED, not compiled as Rust:

- no `Box::new`, no `.clone()`, no ownership concerns inside the macro;
- use binder names in scope: `instantiate!(Nat::S(add(j_prime, k)))`,
  `instantiate!(eq_nat(n, h))`, `instantiate!(List::Cons(h, app(t, y)))`;
- constructors and calls nest freely; one deep hint covers all subterms —
  prefer the outermost missing term;
- placement: inside the failing branch (match the counterexample's
  `branch :` line to the arm), before the tail/IH call;
- a hint may reference only variables bound in that branch.

## 5. Rust-mechanics pitfalls (edits that fail to compile, or panic the pipeline)

1. REAL calls (helpers, IH) ARE compiled Rust: `.clone()` values you reuse,
   deref boxes with `*` (`tip_nine(*i_prime, *j_prime, k)`).
2. A `_` inside a constructor pattern is fine (`Nat::S(_)`; it becomes a
   fresh `_wild_N` binder). A bare `_ =>` arm is allowed after at least one
   constructor arm: it is expanded to the constructors the earlier arms
   leave uncovered, so in a proof body it yields one VC per such
   constructor. A match whose only arm is `_`, or an arm after the `_`
   arm, is rejected.
3. A match target must be a simple variable; to match a boxed tail write
   `match *t.clone() { ... }`. In a FUNCTION body the variable may be
   let-bound to a call (`let s = add(x, y); match s { .. }`), which is how a
   definition branches on a computed value.
4. A `match` inside an `if` branch of a proof body is supported (the
   checking-mode If rule; `tests/if_match_proof.rs` is the regression
   test): split on the guard first, then on the shape, each branch
   carrying only its own facts. The older style — `match` outside and
   BOTH guard-outcomes' facts supplied unconditionally, letting the solver
   split on the guard internally — still works and appears in committed
   proofs (prop_77), but is no longer necessary.
5. After `match *t.clone()`, the original `t` is still usable; clone before
   moves generally — when in doubt, `.clone()` is always safe in proof
   bodies (they are erased logically).
