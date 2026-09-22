# How the source program becomes the SMT query

This file is background: it explains WHY the skill's ground rule holds, by
showing it in the query text. Diagnosis itself happens on the counterexample
file (see `counterexample-format.md`) — never frontier-hunt in the raw
query. The full exemplar quoted below is `../fixtures/prop_09_failed_query.smt2`.

## The pipeline in one paragraph

Type checking walks the proof body: each match arm yields one VC, carrying
the arm's pattern bindings as path conditions and the instantiated
postcondition of every lemma/recursive call as a context fact. Each VC is
then negated, A-normalized (this is where `anf_*` names are born — one per
intermediate value), relationally abstracted (functions become relations —
this is where `*_rel` is born), written to `logs/<goal>_failed_query.smt2`
and solved by cvc5: two processes race on the file, `--full-saturate-quant`
(finds the refutation, `unsat`) and `--finite-model-find` (finds the
countermodel, `sat`); the first definitive answer wins. `sat` means a
countermodel exists: the failure. The counterexample file is projected from data
UPSTREAM of these passes, which is why it contains none of these names.

## Source -> SMT mapping

| Source construct | Encoding |
|---|---|
| `enum Nat` | `(declare-sort UI_Nat 0)` — an uninterpreted sort, deliberately NOT a datatype |
| nullary constructor `Nat::Z` | constant `Nat__Z` |
| constructor `Nat::S(x)` | relation `Nat__S_rel(in, out)` + functionality, injectivity, distinct-from-`Z` axioms |
| function `add` | relation `add_rel(x, y, out)` + functionality axiom; **no totality axiom** |
| one branch of a body | one guarded forall-axiom (read below) |
| an `if` in a branch | TWO axioms sharing the guard term, one per polarity |
| lemma params / pattern binders | skolem constants KEEPING SOURCE NAMES (`i`, `j_prime`) |
| `instantiate!` / auto-collected term | `(assert (exists ...))` chain — a definedness switch |
| path conditions, context facts, negated goal | one final conjunction, in guarded relational form |

Even the lemma itself gets a Unit-valued relation (`tip_nine_rel`) with a
functionality axiom — harmless bookkeeping, ignore it.

## The exemplar query, region by region

**Region 1 — sorts and constructor axioms** (`UI_Nat`, `Nat__Z`,
`Nat__S_rel` + axioms): functionality ("S maps each input to at most
one output"), injectivity, distinctness from `Z`, and acyclicity through a
subterm order `Nat__subterm` (S's input is a proper subterm of its output;
transitive; irreflexive — so `n = S(n)`, `n = S(S(n))`, ... are impossible).
All of these are universal. Note what is NOT here — no axiom says every
`UI_Nat` element is `Z` or an S-image.

**Region 2 — function relations** (`add_rel`, `sub_rel` + functionality
axioms). Again note the absence: nothing asserts an output EXISTS for any
input.

**Region 3 — defining axioms, one per branch.** Read add's S-case slowly;
this is the ground rule made visible:

```smt2
(assert (forall ((y UI_Nat) (x_prime UI_Nat))
  (forall ((anf_0 UI_Nat)) (=> (Nat__S_rel x_prime anf_0)      ; IF S(x') has a value anf_0
    (forall ((anf_1 UI_Nat)) (=> (add_rel anf_0 y anf_1)       ; and add(S(x'), y) has a value anf_1
      (forall ((anf_2 UI_Nat)) (=> (add_rel x_prime y anf_2)   ; and add(x', y) has a value anf_2
        (forall ((anf_3 UI_Nat)) (=> (Nat__S_rel anf_2 anf_3)  ; and S(add(x', y)) has a value anf_3
          (= anf_1 anf_3)))))))))))                            ; THEN anf_1 = anf_3
```

Every step is conditional on a tuple existing. The axiom is
constitutionally incapable of concluding anything about a term that has no
tuple — it does not become false at undefined points, it becomes SILENT.
That is exactly why an absent ledger term makes equations vacuous, and why
adding a switch (a tuple) is the fix.

**Region 4 — skolems.** `i, j, k, i_prime, j_prime` as constants with their
source names (this is what makes the counterexample readable, and what the
ledger's terms are built from). The Unit-typed `_bind_3, v_sub` are proof
plumbing — carriers for sequenced lemma-call facts — ignore them.

**Region 5 — the instantiation block: the ledger, one exists per term.**
Ten ledger terms, ten asserts. Two correspondences:

```smt2
; ledger entry (add j k):
(assert (exists ((anf_21 UI_Nat)) (and (add_rel j k anf_21) true)))
; ledger entry (sub (sub i j) k) -- a NESTED term is a dependency-ordered chain:
(assert (exists ((anf_19 UI_Nat)) (and (sub_rel i j anf_19)
        (exists ((anf_20 UI_Nat)) (and (sub_rel anf_19 k anf_20) true)))))
```

The nested chain is why a deep hint covers its subterms: one switch per
application node, inner first. And the tie-back to this skill's subject:
the deleted hint `S(add(j_prime, k))` would appear here as one more chain —
`exists a. add_rel(j_prime, k, a) ∧ exists s. Nat__S_rel(a, s)`. Its
absence is the entire failure: without that `Nat__S_rel` tuple, Region 3's
S-case axiom stays silent about `add(j, k)`, whose value then floats free
of anything S-shaped.

**Region 6 — the negated VC, one conjunction.** Path conditions
(`∀a. Nat__S_rel(i_prime, a) ⇒ i = a` — the guarded form of
`i == S(i_prime)`), the induction hypothesis (a guarded equality over the
hypothesis's four terms), and the negated goal (a guarded `distinct`). In
the raw query these are all guarded like the axioms; the counterexample
file shows the same facts as plain ground asserts.

## The two deliberate absences (the semantic core)

1. **No totality — except where a definition names the witness.** Nothing
   asserts `∀x̄ ∃r. f_rel(x̄, r)`. Definedness exists where an exists-switch
   was asserted (`instantiate!` is pointwise totality) AND, since 2026-09-18
   (the relabs peephole, `doc/relabs_peephole.md`), where an equation pins a
   call's result to a term: `let x = f(a) in x == t` is emitted as the bare
   literal `f_rel(a, t)` rather than `∀x. f_rel(a,x) ⇒ x = t`. So a
   definitional leaf `f(args) = t` asserts that `f(args)` exists wherever the
   other terms of that leaf exist — the OUTERMOST result of a pinned unfolding
   is always defined, and only the inner terms of a right-hand side (and
   `if`-guard terms) can still be missing. Adding hints remains always sound:
   they are true statements about the real (total) functions, and so is the
   peephole (no existential is written, so EPR is preserved).

2. **No exhaustiveness.** Nothing asserts every `UI_Nat` element is `Z` or
   an S-image, so models may contain junk elements on which no defining
   equation ever fires (their guards never match any constructor tuple).
   Consequence — the skill's boundary: when the frontier is saturated and
   the query is STILL sat, the countermodel lives on junk/unconstrained
   values that no instantiation can reach; the gap is a missing lemma or
   case split. Report and stop (see `theory.md`, fact 3).

Both absences are deliberate: they keep every VC inside a decidable
fragment (EPR). They are the tool's design bet, not an implementation gap.
