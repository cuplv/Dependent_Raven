// List benchmark: associativity of append, proved by structural induction on x.
// This exercises constructor patterns whose fields have DIFFERENT sorts than the
// parent datatype (Cons(Elem, List)), unlike Nat where they coincide.
#[ravencheck::module]
mod list_benchmarks {

    // Uninterpreted element sort (u32 at runtime, abstract sort for the solver).
    #[declare]
    type Elem = u32;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum List {
        Nil,
        Cons(Elem, Box<List>),
    }

    #[val]
    #[recursive]
    fn app(x: List, y: List) -> List {
        match x {
            List::Nil => y,
            List::Cons(h, t) => List::Cons(h, Box::new(app(*t, y))),
        }
    }

    #[val((x: List, y: List, z: List) -> Lemma(app(app(x, y), z) == app(x, app(y, z))))]
    fn app_assoc(x: List, y: List, z: List) {
        match x {
            List::Nil => (),
            List::Cons(h, t) => {
                app_assoc(*t, y, z);
            }
        }
    }
}
