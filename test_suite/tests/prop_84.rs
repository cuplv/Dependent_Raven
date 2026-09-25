// TIP IsaPlanner prop_84:
//   zip(xs, app(ys, zs)) ==
//     app(zip(take(len(ys), xs), ys), zip(drop(len(ys), xs), zs))
//
// Mirror image of prop_83: induction on ys with a case split on xs. In
// the Cons/Cons case both sides are PCons(P(h, y), ·) once that inner term
// is named, around the induction hypothesis at (t, ys', zs).
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
    fn len_b(ys: BList) -> Nat {
        match ys {
            BList::BNil => Nat::Z,
            BList::BCons(_h, t) => Nat::S(Box::new(len_b(*t))),
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
    fn app_b(x: BList, y: BList) -> BList {
        match x {
            BList::BNil => y,
            BList::BCons(h, t) => BList::BCons(h, Box::new(app_b(*t, y))),
        }
    }

    #[val]
    #[recursive]
    fn app_p(x: PList, y: PList) -> PList {
        match x {
            PList::PNil => y,
            PList::PCons(h, t) => PList::PCons(h, Box::new(app_p(*t, y))),
        }
    }

    #[val((xs: AList, ys: BList, zs: BList) ->
        Lemma(zip(xs, app_b(ys, zs)) ==
              app_p(zip(take_a(len_b(ys), xs), ys), zip(drop_a(len_b(ys), xs), zs))))]
    fn tip_84(xs: AList, ys: BList, zs: BList) {
        match ys {
            BList::BNil => (),
            BList::BCons(y, ys_min) => match xs {
                // len_b(ys) == S(len_b(ys')) needs its inner term; then
                // take_a and drop_a of ANil are ANil.
                AList::ANil => {
                    instantiate!(len_b(ys_min));
                }
                AList::ACons(h, t) => {
                    instantiate!(Pair::P(h, y));
                    tip_84(*t, *ys_min, zs);
                }
            },
        }
    }
}
