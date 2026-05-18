use macros::module;

#[module]
#[declare_types(u32)]
mod my_mod {
    use std::collections::HashSet;

    #[declare]
    type MySet = HashSet<u32>;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>)
    }

    #[declare]
    pub fn member(e: u32, s: MySet) -> bool {
        s.contains(&e)
    }

    #[val((a: MySet, b: MySet) -> c: MySet { forall(|e: u32| member(e, c) == (member(e, a) || member(e, b))) })]
    pub fn union(a: MySet, b: MySet) -> MySet {
        a.union(&b).cloned().collect()
    }

    #[lemma((a: MySet, b: MySet) -> Lemma(union(union(a,b), b) == union(a,b)))]
    fn union_idempotent(a: MySet, b: MySet) { 
    }
}
