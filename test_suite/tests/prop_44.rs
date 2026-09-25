// TIP IsaPlanner prop_44: zip(Cons(x, xs), ys) == zip_concat(x, xs, ys)
//
// No induction: zip_concat matches on ys, so a case split on ys lets both
// sides unfold to the same list, once its inner terms P(x, h2) and
// zip(xs, t2) are named.
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

    // TIP's zipConcat (non-recursive).
    #[val]
    fn zip_concat(x: A, xs: AList, ys: BList) -> PList {
        match ys {
            BList::BNil => PList::PNil,
            BList::BCons(h2, t2) => PList::PCons(Pair::P(x, h2), Box::new(zip(xs, *t2))),
        }
    }

    #[val((x: A, xs: AList, ys: BList) -> Lemma(zip(AList::ACons(x, xs), ys) == zip_concat(x, xs, ys)))]
    fn tip_44(x: A, xs: AList, ys: BList) {
        match ys {
            BList::BNil => (),
            BList::BCons(h2, t2) => {
                instantiate!(Pair::P(x, h2));
                instantiate!(zip(xs, t2));
            }
        }
    }
}
