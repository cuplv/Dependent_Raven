# The model file: `test_suite/logs/<lemma>_vc_<k>_model.json`

Written for every goal the solver answers `sat`, from that solving run. Not
written for `unsat` or `UNKNOWN`. The file name gives the lemma and the goal
number. One JSON object, three kinds of entry, in this order:

```json
{
  "Nat":  ["Nat!5", "Nat!1", "Z", "Nat!4"],           // 1. a universe per sort
  "x":    "Nat!3",                                     // 2. a variable's element
  "add":  { "(Nat!2, Nat!3)": "Nat!4", "(Z, Z)": "Z" }, // 3. a table per function
  "S":    { "Nat!1": "Nat!2", "Z": "Nat!1" }           //    and per constructor
}
```

1. **Universes** — one array per sort, in name order: every datatype and every
   `#[declare]`d sort. Elements are nullary constructors by name (`Z`, `Nil`)
   and otherwise tags `Sort!k`. Tags are arbitrary and change between runs;
   only the rows relating them are stable.

2. **Variables** — the goal's binders and the pattern variables the branch
   bound (`_h`, `t`, `n_min`), each mapped to its element. Unit-typed proof
   plumbing is omitted. A goal binder the solver never constrained may be
   missing (known gap).

3. **Relations** — one table per function and per constructor with
   arguments, keyed by argument tuple: `"(a, b)": r`, or a bare `"a": r` for
   one argument. A `bool` function's table has `"true"`/`"false"` on the
   right. A constructor's table maps arguments to the element the
   constructor application denotes. Functions with no row at all are
   omitted.

## Reading rules (the short form is SKILL.md §3)

- A row `f: (a…) → r` is `f_rel(a…, r)` holding in the model: `f(a…)` is
  defined there with value `r`; at most one row per tuple. An absent row means
  the application is undefined at those arguments.
- An element that is the output of a constructor row has a known shape; the
  output of no constructor row and not a nullary constructor is junk.
- The goal: substitute the variables' elements into the `Lemma`. The two
  sides of an `==` map to different elements; a `bool` goal maps to `false`;
  the hypothesis of an `implies` maps to `true` — if only because one of its
  terms is junk, that term is on the walk too.
- Universal rows such as `add: (Z, y) → y` for every `y` come from equations
  with no inner term; they are not named terms and never candidates.

## Not in the file

The list of named terms (the walk does not need it); solver timing; anything
for an `UNKNOWN` goal — no model exists, and this skill stops on that goal.
(The driver also writes `<lemma>_vc_<k>_instantiated_terms.smt2`, a
source-vocabulary script of the goal, the branch and the named terms; it is
not an input of this skill.)
