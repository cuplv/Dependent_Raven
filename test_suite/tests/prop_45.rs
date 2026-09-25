// TIP IsaPlanner prop_45: zip(Cons(x, xs), Cons(y, ys)) == Cons(P(x, y), zip(xs, ys))
//
// One unfolding of zip's Cons/Cons equation; no induction.
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

    #[val((x: A, y: B, xs: AList, ys: BList) ->
        Lemma(zip(AList::ACons(x, xs), BList::BCons(y, ys)) == PList::PCons(Pair::P(x, y), Box::new(zip(xs, ys)))))]
    fn tip_45(_x: A, _y: B, _xs: AList, _ys: BList) {}
}
