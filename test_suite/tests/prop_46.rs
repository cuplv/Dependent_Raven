// TIP IsaPlanner prop_46: zip(Nil, xs) == Nil
//
// One unfolding of zip's Nil equation; no induction. (TIP instantiates
// the first element sort with `Any`; here it is the abstract sort A.)
#[ravencheck::module]
mod tip_benchmarks {

    #[declare]
    type A = u32;

    #[declare]
    type B = u32;

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

    #[val((xs: BList) -> Lemma(zip(AList::ANil, xs) == PList::PNil))]
    fn tip_46(_xs: BList) {}
}
