# Fitting a lemma into the fragment (Extended EPR + relational abstraction)

Every lemma must live inside the decidable fragment the tool enforces:
prenex-universal statements (the `Lemma(...)` wrapper), quantifier-free
bodies over first-order terms, and a relational sort graph that stays
acyclic. This reference is for the exceptional case where a needed fact
does not fit as first conceived.

## Calibration: the recipes' candidates fit BY CONSTRUCTION

A candidate produced by the classification recipes — a generalized guard
instance, an anti-unified endpoint equation, a preservation implication —
is a quantifier-free equation/implication over EXISTING functions. After
the `Lemma` wrapper it is prenex-∀: exactly the supported shape, and it
adds no new sort-graph edges. The moves below are needed only on the
CREATIVE path: when the fact you want mentions an inner quantifier or
requires a new auxiliary function.

## Move 1 — an inner EXISTS becomes a witness function

`exists z. le(x, z) && le(y, z)` is not writable as an ensures. Define
the witness as a program function and name it:

```rust
#[val] #[recursive]
fn max(x: Nat, y: Nat) -> Nat { ... }

#[val((x: Nat, y: Nat) -> Lemma(le(x, max(x, y))))]   // and the y-side twin
```

The existential's content survives; the quantifier disappears into a
`#[val]` definition, which the relational abstraction handles like any
function. (Program-level Skolemization.)

## Move 2 — an inner FORALL becomes a recursive predicate

"every element of `xs` is <= k" is not writable either; a structurally
recursive bool function is:

```rust
#[val] #[recursive]
fn all_le(k: Nat, xs: NList) -> bool {
    match xs {
        NList::Nil => true,
        NList::Cons(h, t) => if le(h, k.clone()) { all_le(k, *t) } else { false },
    }
}
```

Lemmas about the quantified property become lemmas about the predicate;
the predicate's defining equations replace quantifier reasoning by
induction. (This is the `sorted` pattern — the whole benchmark corpus
already works this way.)

## Move 3 — avoid closing a sort cycle

The EPR check rejects queries whose relational sort graph is cyclic, and
a NEW auxiliary function can close a cycle: with `height : Tree -> Nat`
contributing a Tree->Nat edge, defining an auxiliary
`build : Nat -> Tree` adds Nat->Tree and kills the whole module:

```
Found Sort Cycles! This breaks decidability.
```

Responses, in order: restate the fact without the offending direction
(often Move 1's witness can live on the graph's EXISTING side); split
the lemma so the cycle-inducing function is never registered; or accept
that this auxiliary does not fit and report (Stop L3).

## The mechanical signal — the tool referees

Do not try to predict fragment membership. Add the helper and run: a
fragment violation fails FAST and LOUD, before any solving —

- the sort-cycle error above (from the EPR check), or
- a frontend/backend panic for unsupported forms (quantifiers in specs,
  unsupported patterns).

On such an error: retract the helper (it never becomes part of the
proof), apply the applicable move, retry ONCE.

## Stop L3 — fragment rejection

**Criterion.** The reformulated helper — after one pass of the moves —
still triggers the fragment error.

**Response.** Stop. Retract all rejected forms, and report: the
candidate fact (in math notation), each attempted formulation with the
exact error it triggered, and which move was applied between attempts.

```
Fragment rejection for candidate: <fact>.
  attempt 1: fn build(n: Nat) -> Tree ...   -> "Found Sort Cycles: Nat -> Tree -> Nat"
  attempt 2 (Move 3, restated via ...):     -> same cycle
  The fact appears to need a Nat -> Tree function, which this module's
  sort graph cannot admit. Out of scope for this skill.
```

The trigger is the tool's own error message — mechanical, no judgment.
Like L1's report, the attempt list is the diagnostic payload: it tells
the human exactly which direction of expressiveness the proof wanted.
