# Example 6 — no model: the frontier over the ledger (`fixtures/prop_64`)

When the solver answers `UNKNOWN` (or, with a limit set, times out or runs out
of memory) there is no model. The driver still writes
`logs/<lemma>_vc_<k>_instantiated_terms.smt2`, and the procedure falls back to
a frontier search over that file. This example runs it on prop_64's `vc_3`,
whose ledger is identical in form to an UNKNOWN goal's (only the `; verdict:`
line differs), so the result can be checked against example 2's walk.

## The ledger file (header and terms only)

```
; ravencheck instantiated terms
; verdict: sat
; lemma  : tip_64   [vc 3]
; goal   : last(app(xs, Cons(x, Nil))) == x
; branch : xs = Cons(_h, t), t = Cons(_h2, _t2)
;
; definitions:
;   app(Nil, y)                 = y
;   app(Cons(h, t), y)          = Cons(h, app(t, y))
;   last(Nil)                   = Z
;   last(Cons(h, Nil))          = h
;   last(Cons(h, Cons(h2, t2))) = last(Cons(h2, t2))
...
; instantiated terms:
;   from the goal:
;     (Cons x Nil)   (app xs (Cons x Nil))   (last (app xs (Cons x Nil)))
;   from the hypothesis (last (app t (Cons x Nil))) == x:
;     (app t (Cons x Nil))   (last (app t (Cons x Nil)))
;   from patterns:
;     (Cons _h t)   (Cons _h2 _t2)
```

The `branch` line gives the shapes; the `definitions` block gives the equations;
the term groups are what the query has in hand. There is no value information:
nothing says which application is stuck.

## The frontier

One row per application in the ledger whose scrutinee's shape the branch fixes.
Inner terms and guards of the applicable equation that appear in **no** group are
candidates. The outermost result of the equation is never a candidate (the
peephole asserts it once the application and its inner terms exist).

| application | shape (branch) | equation → inner terms | in the ledger? |
|---|---|---|---|
| `app(xs, [x])` | `xs = Cons(_h, t)` | `Cons(_h, app(t, [x]))` → `app(t, [x])` | yes (hypothesis) |
| `app(t, [x])` | `t = Cons(_h2, _t2)` | `Cons(_h2, app(_t2, [x]))` → `app(_t2, [x])` | **no → candidate** |
| `last(app(xs, [x]))` | argument is an application, shape not in the branch | cannot unfold until `app(xs, [x])`'s result is built | — |
| `last(app(t, [x]))` | same | — | — |
| `Cons(x, Nil)`, `Cons(_h, t)`, `Cons(_h2, _t2)` | constructors | no equation | — |

One candidate, `app(_t2, Cons(x, Nil))` — the same as example 2 found from the
model in one lookup. The frontier reached it by unfolding every application in
the ledger; on a large goal that is the cost of this mode.

## Edit and re-run

```rust
NList::Cons(_h2, t2) => {
    instantiate!(app(t2, NList::Cons(x, NList::Nil)));
    tip_64(x, *t);
}
```

Re-run. Three outcomes are possible for a goal that was `UNKNOWN`:

- `unsat` — done; the hint made the goal tractable (an UNKNOWN goal may well
  have been true all along);
- `sat` with a model — switch to model mode for the next round;
- still `UNKNOWN` — the hint now appears under `from the user hints:`; the next
  frontier round unfolds one level deeper from it.

## When to stop

A round whose frontier adds no candidate is **saturation**. Without a model the
three tells of example 5 cannot be read, so the report is only: saturated, no
model, the last frontier table, and the goal. Do not guess a lemma from the
ledger alone.
