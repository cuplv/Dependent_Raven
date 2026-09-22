# The counterexample file, section by section

On every failed VC the verifier writes `logs/<lemma>_vc_<k>_counterexample.smt2`
(relative to `test_suite/`, where the tests run). The file is a valid,
self-contained SMT-LIB script describing the countermodel in SOURCE
vocabulary only — the names you see are the ones written in the proof file.
It is the working artifact for diagnosis. It is never re-run automatically;
running `cvc5 --finite-model-find` on it yields `sat` (the countermodel
exists). Use that configuration, not z3 or plain cvc5: on a satisfiable
query of AVL size z3 does not terminate and cvc5's default answers `unknown`.

The second line of the file is `; verdict: sat` or `; verdict: unknown`.
`sat`: the solver found a countermodel. `unknown`: no answer within the
per-goal time limit; the file has exactly the same content (it is built
from the goal and its ledger, never from a model), so every section below
and the frontier procedure apply unchanged — only the certainty that a
countermodel exists is missing.

Full real instances live in `../fixtures/*_counterexample.smt2`. The
sections, in file order:

## 1. Header (comments)

```smt2
; lemma  : tip_nine   [vc 6]
; goal   : sub(sub(i, j), k) == sub(i, add(j, k))
; branch : i = S(i_prime), j = S(j_prime)
```

- **lemma**: the failing goal `tip_nine_vc_6` split into the source lemma
  name and the VC number. The lemma names a `#[val(... -> Lemma(...))]`
  function in some `test_suite/tests/*.rs` file.
- **goal**: the lemma's ensures, in math notation. For an implication goal
  the line reads `P ==> Q`.
- **branch**: the match arm this VC belongs to, as pattern bindings. This
  is WHERE THE FIX GOES: hints are inserted in exactly this arm of the
  lemma's body. Absent when the VC has no case split (then the body's
  single path is the target).

## 2. Definitions block (comments)

```smt2
; definitions:
;   add(Z, y)            = y
;   add(S(x_prime), y)   = S(add(x_prime, y))
;   count(x, Cons(h, t)) = if eq_nat(x, h) then S(count(x, t)) else count(x, t)
```

One equation per branch of every function the VC mentions. This is the
UNFOLDING RULEBOOK for the frontier walk: to unfold an application one
step, find the equation whose left-hand side pattern matches the known
shape of the scrutinee argument(s), and instantiate its right-hand side.
An `if` right-hand side means the arm compiles to two guarded equations
sharing the guard term (see example 4).

Logical connectives in a definition are shown as written
(`both_zero(a, b) = is_zero(a) && is_zero(b)`, `if p(x) && q(x) then .. else ..`);
each application inside them is an ordinary right-hand-side term and needs a
switch like any other — there is no special guard rule for `&&`/`||`.

A `let` in a function body is shown inlined (`pick(x, y) = if is_zero(add(x, y))
then add(y, x) else add(x, y)`), so its call appears as an ordinary application
and needs a switch like any other. When the body matches on the bound name, the
equation keeps the `let` and the `match` on one line
(`f(x, y) = let s = add(x, y) in match s { Z => .., S(p) => .. }`): the arm
taken is decided by the shape of `add(x, y)`, so that application must have a
switch, and its one-step result pins which arm's right-hand side applies.

## 3. Declarations

Sorts (`declare-sort`), all constructors of every used datatype (declared
even when no term mentions them — a path condition may), functions with
source arities, then the goal's input variables. Notes: an uninterpreted
sort (e.g. `Elem`) is just another `declare-sort`; a source sort colliding
with an SMT-LIB built-in is written with a trailing underscore and a comment
says so (`List` -> `List_`) — cosmetic only.

## 4. Path-condition asserts

```smt2
(assert (= i (S i_prime)))
```

The branch line, as ground equalities. These are the shape facts the
frontier's pinning test uses.

## 5. Instantiated-terms ledger (comments) — THE key section

```smt2
; instantiated terms:
;   from the goal:            ...terms...
;   from the hypothesis <fact>:  ...terms...
;   from patterns:            ...terms...
;   user hints (instantiate!): ...terms...
```

Every term with a definedness switch in the failed query, grouped by
origin:

- **from the goal** — auto-collected from the ensures.
- **from the hypothesis `<fact>`** — one group per fact in the VC's
  context; a fact is the instantiated postcondition of a recursive
  self-call (the induction hypothesis) or of a helper-lemma call. The
  group is labeled by the fact itself.
- **from patterns** — the constructor terms of the branch line.
- **user hints (instantiate!)** — terms provided manually that no other
  origin explains.

Reading rules: a term's presence switches ALL its subterms too (deep terms
cover their subterms). A term NOT in any group has no switch — defining
equations that mention it cannot fire. The coverage pre-check reads this
section: a branch-line pattern variable appearing in no hypothesis group
signals a missing recursive call, not a missing instantiation.

## 6. Negated goal

```smt2
(assert (distinct (sub (sub i j) k) (sub i (add j k))))
(check-sat)
```

`distinct` for an equality goal; `(= <atom> false)` for a bare-predicate
goal; for an implication goal the peeled antecedents appear just above as
holding facts (`(= P true)` or an equality) — in the countermodel the
antecedent holds and only the conclusion fails.

## What is NOT in the file (current stage)

The emitter currently produces the skeleton: no "equalities holding in the
countermodel" section and no LHS/RHS evaluation traces yet. Diagnosis
therefore combines section 2 (the rulebook) with section 5 (the switches):
that is exactly the frontier walk in SKILL.md. When later emitter stages
add the equalities/trace sections, they pre-compute part of that walk; the
ledger reading stays the same.
