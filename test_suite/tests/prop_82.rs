// TIP IsaPlanner prop_82: take(n, zip(xs, ys)) == zip(take(n, xs), take(n, ys))
//
// The take twin of prop_58: induction on n with case splits on xs and ys.
// The Cons/Cons case needs zip's inner term P(h, h2) named, after which
// both sides are PCons(P(h, h2), ·) around the induction hypothesis.
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
    fn take_a(n: Nat, xs: AList) -> AList {
        match n {
            Nat::Z => AList::ANil,
            Nat::S(n_min) => match xs {
                AList::ANil => AList::ANil,
                AList::ACons(h, t) => AList::ACons(h, Box::new(take_a(*n_min, *t))),
            },
        }
    }

    #[val]
    #[recursive]
    fn take_b(n: Nat, ys: BList) -> BList {
        match n {
            Nat::Z => BList::BNil,
            Nat::S(n_min) => match ys {
                BList::BNil => BList::BNil,
                BList::BCons(h, t) => BList::BCons(h, Box::new(take_b(*n_min, *t))),
            },
        }
    }

    #[val]
    #[recursive]
    fn take_p(n: Nat, ps: PList) -> PList {
        match n {
            Nat::Z => PList::PNil,
            Nat::S(n_min) => match ps {
                PList::PNil => PList::PNil,
                PList::PCons(h, t) => PList::PCons(h, Box::new(take_p(*n_min, *t))),
            },
        }
    }

    #[val((n: Nat, xs: AList, ys: BList) ->
        Lemma(take_p(n, zip(xs, ys)) == zip(take_a(n, xs), take_b(n, ys))))]
    fn tip_82(n: Nat, xs: AList, ys: BList) {
        match n {
            Nat::Z => (),
            Nat::S(n_min) => match xs {
                AList::ANil => (),
                AList::ACons(h, t) => match ys {
                    // take_a(S(n'), ACons(h, t)) unfolds to ACons(h, take_a(n', t)),
                    // and zip of that with BNil is PNil.
                    BList::BNil => {
                        instantiate!(take_a(n_min, t));
                    }
                    BList::BCons(h2, t2) => {
                        instantiate!(Pair::P(h, h2));
                        tip_82(*n_min, *t, *t2);
                    }
                },
            },
        }
    }
}
