// TIP IsaPlanner prop_85:
//   implies(len(xs) == len(ys), zip(rev(xs), rev(ys)) == rev(zip(xs, ys)))
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
    fn len_b(ys: BList) -> Nat {
        match ys {
            BList::BNil => Nat::Z,
            BList::BCons(_h, t) => Nat::S(Box::new(len_b(*t))),
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

    #[val]
    #[recursive]
    fn rev_a(xs: AList) -> AList {
        match xs {
            AList::ANil => AList::ANil,
            AList::ACons(h, t) => app_a(rev_a(*t), AList::ACons(h, Box::new(AList::ANil))),
        }
    }

    #[val]
    #[recursive]
    fn rev_b(ys: BList) -> BList {
        match ys {
            BList::BNil => BList::BNil,
            BList::BCons(h, t) => app_b(rev_b(*t), BList::BCons(h, Box::new(BList::BNil))),
        }
    }

    #[val]
    #[recursive]
    fn rev_p(ps: PList) -> PList {
        match ps {
            PList::PNil => PList::PNil,
            PList::PCons(h, t) => app_p(rev_p(*t), PList::PCons(h, Box::new(PList::PNil))),
        }
    }

    // Helper: appending one element adds one to the length (A side).
    #[val((xs: AList, x: A) -> Lemma(len_a(app_a(xs, AList::ACons(x, Box::new(AList::ANil)))) == Nat::S(len_a(xs))))]
    fn len_app_one_a(xs: AList, x: A) {
        match xs {
            AList::ANil => (),
            AList::ACons(_h, t) => len_app_one_a(*t, x),
        }
    }

    // Helper: rev preserves length (A side).
    #[val((xs: AList) -> Lemma(len_a(rev_a(xs)) == len_a(xs)))]
    fn len_rev_a(xs: AList) {
        match xs {
            AList::ANil => (),
            AList::ACons(h, t) => {
                len_app_one_a(rev_a(*t.clone()), h);
                len_rev_a(*t);
            }
        }
    }

    // Helper: appending one element adds one to the length (B side).
    #[val((ys: BList, y: B) -> Lemma(len_b(app_b(ys, BList::BCons(y, Box::new(BList::BNil)))) == Nat::S(len_b(ys))))]
    fn len_app_one_b(ys: BList, y: B) {
        match ys {
            BList::BNil => (),
            BList::BCons(_h, t) => len_app_one_b(*t, y),
        }
    }

    // Helper: rev preserves length (B side).
    #[val((ys: BList) -> Lemma(len_b(rev_b(ys)) == len_b(ys)))]
    fn len_rev_b(ys: BList) {
        match ys {
            BList::BNil => (),
            BList::BCons(h, t) => {
                len_app_one_b(rev_b(*t.clone()), h);
                len_rev_b(*t);
            }
        }
    }

    // Helper: for lists of equal length, zip commutes with appending one
    // element to each. The length hypothesis is refuted in the mixed
    // Nil/Cons cases once the tail's length is a term.
    #[val((xs: AList, ys: BList, x: A, y: B) ->
        Lemma(implies(len_a(xs) == len_b(ys),
                      zip(app_a(xs, AList::ACons(x, Box::new(AList::ANil))),
                          app_b(ys, BList::BCons(y, Box::new(BList::BNil))))
                      == app_p(zip(xs, ys), PList::PCons(Pair::P(x, y), Box::new(PList::PNil))))))]
    fn zip_app_one(xs: AList, ys: BList, x: A, y: B) {
        match xs {
            AList::ANil => match ys {
                BList::BNil => (),
                BList::BCons(_h2, t2) => {
                    instantiate!(len_b(t2));
                }
            },
            AList::ACons(h, t) => match ys {
                BList::BNil => {
                    instantiate!(len_a(t));
                }
                BList::BCons(h2, t2) => {
                    instantiate!(Pair::P(h, h2));
                    zip_app_one(*t, *t2, x, y);
                }
            },
        }
    }

    // Induction on xs with a case split on ys; the mixed Nil/Cons cases
    // refute the length hypothesis once the tail's length is a term. In the
    // Cons/Cons case rev of each side appends one element, zip_app_one (at
    // rev_a(t), rev_b(t2), whose lengths agree by len_rev_a/len_rev_b and the
    // hypothesis) moves the pair P(h, h2) to the end, and the induction
    // hypothesis rewrites zip(rev_a(t), rev_b(t2)) to rev_p(zip(t, t2)).
    #[val((xs: AList, ys: BList) ->
        Lemma(implies(len_a(xs) == len_b(ys), zip(rev_a(xs), rev_b(ys)) == rev_p(zip(xs, ys)))))]
    fn tip_85(xs: AList, ys: BList) {
        match xs {
            AList::ANil => match ys {
                BList::BNil => (),
                BList::BCons(_h2, t2) => {
                    instantiate!(len_b(t2));
                }
            },
            AList::ACons(h, t) => match ys {
                BList::BNil => {
                    instantiate!(len_a(t));
                }
                BList::BCons(h2, t2) => {
                    len_rev_a(*t.clone());
                    len_rev_b(*t2.clone());
                    zip_app_one(rev_a(*t.clone()), rev_b(*t2.clone()), h, h2);
                    tip_85(*t, *t2);
                }
            },
        }
    }
}
