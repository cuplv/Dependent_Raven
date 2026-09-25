// TIP IsaPlanner prop_83:
//   zip(app(xs, ys), zs) ==
//     app(zip(xs, take(len(xs), zs)), zip(ys, drop(len(xs), zs)))
//
// Induction on xs with a case split on zs. In the Cons/Nil case the right
// side ends in zip(ys, BNil), which needs the shape of ys (zip matches its
// first argument). In the Cons/Cons case both sides are PCons(P(h, z), ·)
// once that inner term is named, around the induction hypothesis at
// (t, ys, zs').
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
    fn len_a(xs: AList) -> Nat {
        match xs {
            AList::ANil => Nat::Z,
            AList::ACons(_h, t) => Nat::S(Box::new(len_a(*t))),
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
    fn app_a(x: AList, y: AList) -> AList {
        match x {
            AList::ANil => y,
            AList::ACons(h, t) => AList::ACons(h, Box::new(app_a(*t, y))),
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

    #[val((xs: AList, ys: AList, zs: BList) ->
        Lemma(zip(app_a(xs, ys), zs) ==
              app_p(zip(xs, take_b(len_a(xs), zs)), zip(ys, drop_b(len_a(xs), zs)))))]
    fn tip_83(xs: AList, ys: AList, zs: BList) {
        match xs {
            AList::ANil => (),
            AList::ACons(h, t) => match zs {
                // len_a(xs) == S(len_a(t)) and app_a(xs, ys) == ACons(h, app_a(t, ys))
                // need their inner terms; then take/drop of BNil are BNil and
                // zip(ys, BNil) needs the shape of ys.
                BList::BNil => {
                    instantiate!(len_a(t));
                    instantiate!(app_a(t, ys));
                    match ys {
                        AList::ANil => (),
                        AList::ACons(_h2, _t2) => (),
                    }
                }
                BList::BCons(z, zs_min) => {
                    instantiate!(Pair::P(h, z));
                    tip_83(*t, ys, *zs_min);
                }
            },
        }
    }
}
