# The model file: `test_suite/logs/<lemma>_vc_<k>_model.json`

Written for every goal the solver answers `sat`, from the very run that produced
the answer. Not written for `unsat` (nothing to show) or `UNKNOWN` (no model
exists; there is nothing to read — report it). The file name gives the lemma and
the goal number. Together with the source file it is the only input the
procedure needs.

Running example, the lemma `add(S(S(Z)), x) == S(S(x))` with an empty body:

```json
{
  "Nat": ["Nat!5", "Nat!1", "Nat!6", "Nat!3", "Nat!2", "Z", "Nat!4"],
  "x": "Nat!3",
  "add": {
    "(Nat!2, Nat!3)": "Nat!4",
    "(Z, Nat!5)": "Nat!5", "(Z, Nat!1)": "Nat!1", "(Z, Nat!6)": "Nat!6",
    "(Z, Nat!3)": "Nat!3", "(Z, Nat!2)": "Nat!2", "(Z, Z)": "Z", "(Z, Nat!4)": "Nat!4"
  },
  "S": { "Nat!5": "Nat!6", "Nat!1": "Nat!2", "Nat!3": "Nat!5", "Z": "Nat!1" }
}
```

## The three sections

1. **Universes** — one array per sort, in name order: every datatype (`Nat`,
   `NList`) and every `#[declare]`d sort (`Elem`, `A`). Elements are the nullary
   constructors by name (`Z`, `Nil`) and otherwise tags `Sort!k`. The tags are
   arbitrary and change from run to run; only the rows relating them matter.

2. **Variables** — the goal's binders (`x`, `xs`) and the pattern variables the
   branch bound (`_h`, `t`, `n_min`), each mapped to its element. Unit-typed proof
   plumbing is omitted.

3. **Relations** — one finite table per function and per constructor with
   arguments, keyed by argument tuple: `"(a, b)": r`, or a bare `"a": r` for one
   argument. A `bool` function's table has `"true"`/`"false"` on the right. A
   constructor's table (`S`, `Cons`, `P`) maps arguments to the element the
   constructor application denotes.

## What a row means

`f: (a₁, …, aₙ) → r` says the relation `f_rel(a₁, …, aₙ, r)` holds in the model:
the application `f(a₁, …, aₙ)` is *defined* there and its value is `r`. There is
at most one row per argument tuple (functionality). A row is present for one of
three reasons, and the file does not say which:

- the application is a **named term** — it occurs in the goal, in a hypothesis
  (an induction hypothesis or a helper call), or in an `instantiate!` hint. In the
  example `(Nat!2, Nat!3) → Nat!4` is the goal's `add(S(S(Z)), x)`;
- it is covered by a defining equation with **no inner term**, which holds
  universally. `add(Z, y) = y` is such an equation: that is why `(Z, y) → y`
  appears for every element `y`. Likewise `le(Z, y) = true`, `take(Z, xs) = Nil`,
  `drop(Z, xs) = xs`, `zip(Nil, ys) = Nil`;
- the solver made it true **arbitrarily** (it may, wherever nothing constrains it).

An **absent** row means the model asserts nothing about `f` at those arguments:
the application is undefined there, so no equation mentioning it can fire. This
absence — at an application the branch needs — is the only fact the procedure
acts on. It never needs to know which present rows are named.

## Shapes and junk

An element that is the **output** of some constructor row has a known shape:
`Nat!1` is `S(Z)`, `Nat!2` is `S(S(Z))`, `Nat!5` is `S(x)`, `Nat!6` is `S(S(x))`.
An element that is the output of **no** constructor row is *junk*: nothing says
what it is. `Nat!4` above is junk, and it is the value of `add(S(S(Z)), x)` — the
goal's left side — which is how the model refutes the goal (`Nat!4 ≠ Nat!6`).

A function result that is junk although its argument's shape is known is the
signature of an unfired equation: `add(S(S(Z)), x)` should be `S(add(S(Z), x))`,
but `add(S(Z), x)` — the inner term of that equation — has no row `(Nat!1, Nat!3)`,
so the equation has nothing to apply to.

## Reading the branch back

The `branch` of a goal (which match arms it lives in) is recoverable from the
variables and the constructor rows: with `xs = NList!1`, `_h = Nat!1`,
`t = NList!3` and the row `Cons: (Nat!1, NList!3) → NList!1`, the branch is
`xs = Cons(_h, t)`. A pattern variable that is itself the output of no
constructor row is one the branch does *not* fix (its shape is unknown).

## Reading the goal

Substitute the variables' elements into the `Lemma(...)` of the source and look
each application up. Every application of the goal has a row (it is a named
term). The two sides of an `==` map to different elements; a `bool` goal maps to
`false`; the hypothesis of an `implies` maps to `true`.

## What the model does not contain

- The list of named terms (the ledger). Not needed: the procedure walks from the
  goal through the definitions and asks only whether the next row exists.
- Any timing or solver detail. The model is the finite model of the one run that
  answered `sat` (z3, in process).
- For an `UNKNOWN` goal: nothing — no model file is written.

After a re-run with hints added, the new model shows those applications as rows,
and the walk continues one level deeper from them.

## The companion file: `<lemma>_vc_<k>_instantiated_terms.smt2`

Written for every failing goal, `sat` or `UNKNOWN` (its `; verdict:` line says
which), from the goal and its instantiation list alone — never from a model. Its
header gives `lemma`, `goal`, `branch` and a `definitions` block (the source's
equations in math notation); its `; instantiated terms:` groups list the
applications the query has in hand — from the goal, from each hypothesis, from
the patterns, and from the user hints. It is the ledger the frontier method
works on when no model exists (SKILL.md §7). With a model present it is not
needed: every named term has a row, and the walk reads the branch and the goal
from the model and the source.

