// TIP IsaPlanner prop_58: drop(n, zip(xs, ys)) == zip(drop(n, xs), drop(n, ys))
//
// The first zip benchmark: two uninterpreted element sorts, a Pair type
// and three list types. Induction on n with case splits on xs and ys in
// the S step. The Cons/Nil case needs the shape of drop(n', t) because
// zip matches its first argument first (zip(_, Nil) unfolds only once
// its first argument is Nil or Cons); the Cons/Cons case is the
// induction hypothesis at (n', t, t2).
#[ravencheck::module]
mod tip_benchmarks {

    #[declare]
    type A = u32;

    #[declare]
    type B = u32;

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum AList {
        ANil,
        ACons(A, Box<AList>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum BList {
        BNil,
        BCons(B, Box<BList>),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Pair {
        P(A, B),
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum PList {
        PNil,
        PCons(Pair, Box<PList>),
    }

    #[val]
    #[recursive]
    fn zip(xs: AList, ys: BList) -> PList {
        match xs {
            AList::ANil => PList::PNil,
            AList::ACons(h, t) => match ys {
                BList::BNil => PList::PNil,
                BList::BCons(h2, t2) => PList::PCons(Pair::P(h, h2), Box::new(zip(*t, *t2))),
            },
        }
    }

    #[val]
    #[recursive]
    fn drop_a(n: Nat, xs: AList) -> AList {
        match n {
            Nat::Z => xs,
            Nat::S(n_min) => match xs {
                AList::ANil => AList::ANil,
                AList::ACons(_h, t) => drop_a(*n_min, *t),
            },
        }
    }

    #[val]
    #[recursive]
    fn drop_b(n: Nat, ys: BList) -> BList {
        match n {
            Nat::Z => ys,
            Nat::S(n_min) => match ys {
                BList::BNil => BList::BNil,
                BList::BCons(_h, t) => drop_b(*n_min, *t),
            },
        }
    }

    #[val]
    #[recursive]
    fn drop_p(n: Nat, ps: PList) -> PList {
        match n {
            Nat::Z => ps,
            Nat::S(n_min) => match ps {
                PList::PNil => PList::PNil,
                PList::PCons(_h, t) => drop_p(*n_min, *t),
            },
        }
    }

    #[val((n: Nat, xs: AList, ys: BList) ->
        Lemma(drop_p(n, zip(xs, ys)) == zip(drop_a(n, xs), drop_b(n, ys))))]
    fn tip_58(n: Nat, xs: AList, ys: BList) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => match xs {
                AList::ANil => (),
                AList::ACons(h, t) => match ys {
                    // zip(drop_a(n', t), BNil) unfolds only once drop_a(n', t)
                    // has a known shape.
                    BList::BNil => match drop_a(*n_min, *t) {
                        AList::ANil => (),
                        AList::ACons(_h2, _t2) => (),
                    },
                    BList::BCons(h2, t2) => {
                        // Inner term: zip's Cons equation builds the pair P(h, h2).
                        instantiate!(Pair::P(h, h2));
                        tip_58(*n_min, *t, *t2);
                    }
                },
            },
        }
    }
}
