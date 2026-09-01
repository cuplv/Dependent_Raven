# Example 3 — Multiple call sites: one equation, two stuck applications

The same defining equation can be stuck at SEVERAL call sites, yielding one
candidate per site. Each candidate alone is insufficient — the round's
candidates form a set, and the proof needs the whole set.

## Broken proof

`app_assoc` (list append associativity): induction skeleton and induction
hypothesis intact; both hints missing. `Elem` is an uninterpreted element
sort; `List` is a list of `Elem`.

```rust
#[val((x: List, y: List, z: List) -> Lemma(app(app(x, y), z) == app(x, app(y, z))))]
fn app_assoc(x: List, y: List, z: List) {
    match x {
        List::Nil => (),
        List::Cons(h, t) => {
            app_assoc(*t, y, z);
        }
    }
}
```

```
$ cargo test --test prop_list_append
## > Failed to verify 'app_assoc_vc_5': solver found counterexamples.
## > 💾 Counterexample: logs/app_assoc_vc_5_counterexample.smt2
```

## Counterexample

```smt2
; ravencheck counterexample
; lemma  : app_assoc   [vc 5]
; goal   : app(app(x, y), z) == app(x, app(y, z))
; branch : x = Cons(h, t)
;
; definitions:
;   app(Nil, y)        = y
;   app(Cons(h, t), y) = Cons(h, app(t, y))

(declare-sort Elem 0)
; sort 'List' is written as 'List_' below (the name collides with a Z3 built-in)
(declare-sort List_ 0)
(declare-const Nil List_)
(declare-fun Cons (Elem List_) List_)
(declare-fun app (List_ List_) List_)

(declare-const x List_)
(declare-const z List_)
(declare-const y List_)
(declare-const h Elem)
(declare-const t List_)

(assert (= x (Cons h t)))

; instantiated terms:
;   from the goal:
;     (app y z)   (app x y)   (app (app x y) z)   (app x (app y z))
;   from the hypothesis (app (app t y) z) == (app t (app y z)):
;     (app t y)   (app (app t y) z)   (app t (app y z))
;   from patterns:
;     (Cons h t)

(assert (distinct (app (app x y) z) (app x (app y z))))
(check-sat)
```

(The `List_` rename is cosmetic: the source sort `List` collides with a Z3
built-in, so the file writes it with a trailing underscore and says so.)

## Reasoning

**Coverage pre-check.** The branch binds `h` and `t`; the hypothesis group
mentions `t` (the recursive call on the tail). Not a missing-recursive-call
failure. Proceed.

**Frontier round.**

| Ledger application | Scrutinee | Shape known? | One-step result | Absent terms |
|---|---|---|---|---|
| `(app x y)` | `x` (app matches arg 1) | yes: `x = Cons(h, t)` | `Cons(h, app(t, y))` | **`Cons(h, app(t, y))`** (`app(t, y)` is in the ledger) |
| `(app x (app y z))` | `x` | yes: `x = Cons(h, t)` | `Cons(h, app(t, app(y, z)))` | **`Cons(h, app(t, app(y, z)))`** (`app(t, app(y, z))` is in the ledger) |
| `(app (app x y) z)` | `app(x, y)` — a function result, no shape | no | — | — |
| `(app y z)` | `y` — bare variable | no | — | — |
| hypothesis-group terms | scrutinees `t`, `app(t, y)` — bare / function result | no | — | — |

No `if` in the definition, so no guard-term candidates.

**Result: two candidates — the SAME Cons-equation stuck at two different
call sites.** `app(x, y)` (the goal's left side) and `app(x, app(y, z))`
(the goal's right side) each need their own wrapped result. The candidates
are one per call site, and they are jointly necessary: with only one added,
one side of the goal connects and the other still floats — verified by
re-checking the query with each candidate's witnesses alone (`sat` both
times) and with both (`unsat`). Add the full set.

Note on hint depth: `Cons(h, app(t, app(y, z)))` covers its subterms —
`app(t, app(y, z))` and `app(y, z)` need no separate hints (here they were
already in the ledger anyway). When candidates nest, prefer the outermost.

## Fix

Both hints in the failing branch, before the recursive call:

```rust
        List::Cons(h, t) => {
            instantiate!(List::Cons(h, app(t, y)));
            instantiate!(List::Cons(h, app(t, app(y, z))));
            app_assoc(*t, y, z);
        }
```

## Verified

```
$ cargo test --test prop_list_append
test tip_benchmarks_tests::check_properties ... ok
```

Minimization check: each hint alone leaves the VC failing; both are needed.
