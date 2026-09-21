// `#[declare] fn`: an uninterpreted function. The verifier sees only its
// signature (a relation with the functionality axiom, no definitional
// equations); the Rust body is ordinary compiled code it never reads.
#[ravencheck::module]
mod declare_fn {

    #[declare]
    type Num = u32;

    #[declare]
    fn plus(a: Num, b: Num) -> Num {
        a.wrapping_add(b)
    }

    #[declare]
    fn is_zero(a: Num) -> bool {
        a == 0
    }

    // A defined function may call a declared one.
    #[val]
    fn double(x: Num) -> Num {
        plus(x, x)
    }

    // A declared function may guard a definition.
    #[val]
    fn zero_or(x: Num, y: Num) -> Num {
        if is_zero(x) { x } else { y }
    }

    #[val((x: Num) -> Lemma(double(x) == plus(x, x)))]
    fn double_unfolds(x: Num) {}

    // Functionality is all that is known: equal arguments give equal results.
    #[val((a: Num, b: Num, c: Num) -> Lemma(implies(a == b, plus(a, c) == plus(b, c))))]
    fn plus_congruent(a: Num, b: Num, c: Num) {}

    #[val((x: Num, y: Num) -> Lemma(implies(is_zero(x), zero_or(x, y) == x)))]
    fn zero_or_hit(x: Num, y: Num) {}
}
