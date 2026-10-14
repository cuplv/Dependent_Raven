# Example 6 — missing induction hypothesis: tested first

prop_47, `height(mirror(t)) == height(t)`; `max_comm` proven and called, the
IH called on `l` only. `tip_47_vc_2`, branch `t = Node(l, e, r)`. Instantiate
skill: STOP, goal term `height(mirror(t))`, stuck at `mirror(r)` with `r` a
variable the branch does not fix.

```json
"l": "Tree!2", "r": "Tree!1",
"mirror": { "Tree!2": "Tree!4", "Tree!1": "Tree!3" },
"height": { "Tree!2": "Nat!4", "Tree!4": "Nat!4", "Tree!1": "Nat!5", "Tree!3": "Nat!2" },
"max":    { "(Nat!4, Nat!5)": "Nat!6", "(Nat!5, Nat!4)": "Nat!6", "(Nat!2, Nat!4)": "Nat!3" }
```

Every equation fired (`mirror(t)`, both `height`s, `max_comm`); the IH on `l`
holds (`Nat!4 = Nat!4`); the single free value is `height(mirror r) = Nat!2
≠ height(r) = Nat!5`.

The stop looks like a case split (example 3) and the endpoints like an
algebraic gap (example 1); both fixes would be wrong — a `match r` gives
`mirror(r)` a shape, not a height, and `height(mirror(x)) == height(x)` as a
helper is the target itself. **Missing IH**: `r` is a pattern variable of
the inductive sort and the goal instantiated at `r` appears in **no**
hypothesis — only the goal at `l` does. Mention is not the test (`r` occurs
in `max_comm`'s call); the instantiated goal is.

```rust
Tree::Node(l, e, r) => {
    tip_47(*l.clone());
    tip_47(*r.clone());   // added: r ⊏ t via Node(l, e, r)
    max_comm(height(*l), height(*r));
}
```

Green. Report: self-call on `r` — missing IH — `r ⊏ t via Node(l, e, r)` —
depth 0.

Tell: both goal sides built from constructor rows, one application of the
goal's own function free at a pattern variable. Check every inductive
pattern variable for its instantiated goal before reading the stop any
other way.
