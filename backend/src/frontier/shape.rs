//! [KOR] 모양 환경: 항 -> 그 항이 같다고 알려진 생성자 적용. 정의 등식은 scrutinee의
//!       생성자 모양에 대해서만 발화하므로, 전개기는 인자를 알려진 모양으로 바꾼 뒤
//!       등식의 패턴과 맞춥니다. 모양의 출처는 셋: 분기의 패턴 등식(`xs == Cons(h, t)`),
//!       goal/가설 안의 생성자 리터럴, 그리고 이미 발화한 등식의 생성자 결과
//!       (`len(xs) ↦ S(len(t))`, 파생 모양).
//! [ENG] The shape environment: term -> the constructor application it is known to
//!       equal. A defining equation fires only against a constructor shape at its
//!       scrutinee positions, so the unroller rewrites arguments with known shapes
//!       before matching them against an equation's patterns. Three sources: the
//!       branch's pattern equalities (`xs == Cons(h, t)`), constructor literals in
//!       the goal or hypotheses (their own shape), and the constructor result of an
//!       equation that already fired (`len(xs) ↦ S(len(t))`, a derived shape).

use frontend::ast::Expr;

use crate::cex::dissect::{Core, VcParts};

/// [ENG] Bound on nested shape expansion. Pattern equalities nest as deep as the
///       proof's `match`es (two or three in practice); the bound only matters for a
///       cyclic derived shape, which a non-structural definition could produce.
const EXPAND_FUEL: usize = 8;

#[derive(Debug, Default, Clone)]
pub struct Shapes {
    /// [ENG] `(term, constructor application)`, first entry wins.
    known: Vec<(Expr, Expr)>,
}

fn is_constructor(t: &Expr) -> bool {
    matches!(t, Expr::Constructor { .. })
}

/// [ENG] `x == C(..)` or `C(..) == x`, as `(x, C(..))`.
fn as_shape_equality(e: &Expr) -> Option<(Expr, Expr)> {
    if let Expr::BinOp { op: frontend::ast::BinOp::Eq, left, right } = e {
        if is_constructor(right) && !is_constructor(left) {
            return Some(((**left).clone(), (**right).clone()));
        }
        if is_constructor(left) && !is_constructor(right) {
            return Some(((**right).clone(), (**left).clone()));
        }
    }
    None
}

impl Shapes {
    /// [KOR] goal에서 모양을 모읍니다: 분기의 패턴 등식, goal의 전건(`implies` 가정,
    ///       예: `ys == Nil`), 그리고 가설 중 한쪽이 생성자 적용인 등식.
    /// [ENG] Seeds the environment from a dissected goal: the branch's pattern
    ///       equalities, the goal's peeled assumptions (`ys == Nil` in an
    ///       `implies`), and any hypothesis equality with a constructor side.
    pub fn from_goal(parts: &VcParts) -> Shapes {
        let mut shapes = Shapes::default();
        shapes.seed_from(parts);
        shapes
    }

    /// [ENG] Adds the goal's shapes to an existing environment (idempotent: an
    ///       existing shape is kept), so a round can be run on any environment and
    ///       derived shapes survive across rounds.
    pub fn seed_from(&mut self, parts: &VcParts) {
        let mut equalities: Vec<&Expr> = parts.path_conds.iter().collect();
        equalities.extend(parts.goal.assumptions.iter());
        for h in &parts.hypotheses {
            equalities.push(&h.fact);
        }
        for e in equalities {
            if let Some((t, c)) = as_shape_equality(e) {
                self.insert(t, c);
            }
        }
    }

    fn insert(&mut self, t: Expr, c: Expr) {
        if is_constructor(&t) || !is_constructor(&c) {
            return;
        }
        if self.lookup(&t).is_none() {
            self.known.push((t, c));
        }
    }

    fn lookup(&self, t: &Expr) -> Option<&Expr> {
        self.known.iter().find(|(k, _)| k == t).map(|(_, c)| c)
    }

    /// [KOR] 이미 발화한 등식의 생성자 결과를 기록합니다 (`len(xs) ↦ S(len(t))`).
    ///       생성자 적용이 아닌 결과는 모양이 아니므로 무시합니다.
    /// [ENG] Records the constructor result of an equation that fired. A result that
    ///       is not a constructor application is no shape and is ignored; an existing
    ///       shape is never overridden.
    pub fn add_derived(&mut self, t: Expr, result: Expr) {
        self.insert(t, result);
    }

    /// [ENG] The constructor application `t` is known to equal: a constructor
    ///       application is its own shape; otherwise the recorded one, if any.
    pub fn shape_of<'a>(&'a self, t: &'a Expr) -> Option<&'a Expr> {
        if is_constructor(t) {
            Some(t)
        } else {
            self.lookup(t)
        }
    }

    /// [KOR] 알려진 모양을 항 안에 끝까지(연료 한도 내에서) 대입합니다:
    ///       `xs`에 `xs ↦ Cons(h, t)`, `t ↦ Cons(h2, t2)`면 `Cons(h, Cons(h2, t2))`.
    /// [ENG] Substitutes known shapes throughout `t`, to the fuel bound: with
    ///       `xs ↦ Cons(h, t)` and `t ↦ Cons(h2, t2)`, `xs` becomes
    ///       `Cons(h, Cons(h2, t2))`. Applications are expanded inside first, then
    ///       looked up both as written and as expanded.
    pub fn expand(&self, t: &Expr) -> Expr {
        self.expand_fuel(t, EXPAND_FUEL)
    }

    fn expand_fuel(&self, t: &Expr, fuel: usize) -> Expr {
        if fuel == 0 {
            return t.clone();
        }
        match t {
            Expr::Var(_) => match self.lookup(t) {
                Some(c) => self.expand_fuel(c, fuel - 1),
                None => t.clone(),
            },
            Expr::Constructor { name, args } => Expr::Constructor {
                name: name.clone(),
                args: args.iter().map(|a| self.expand_fuel(a, fuel)).collect(),
            },
            Expr::Call { func, args } => {
                let expanded = Expr::Call {
                    func: func.clone(),
                    args: args.iter().map(|a| self.expand_fuel(a, fuel)).collect(),
                };
                match self.lookup(&expanded).or_else(|| self.lookup(t)) {
                    Some(c) => self.expand_fuel(c, fuel - 1),
                    None => expanded,
                }
            }
            other => other.clone(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.known.is_empty()
    }
}

/// [ENG] The goal's core and assumptions as expressions, for callers that walk the
///       goal (step 4); here only to keep `Core` handling in one place.
pub fn goal_atoms(parts: &VcParts) -> Vec<&Expr> {
    let mut out: Vec<&Expr> = parts.goal.assumptions.iter().collect();
    match &parts.goal.core {
        Core::Eq(l, r) => {
            out.push(l);
            out.push(r);
        }
        Core::Bool(a) | Core::Opaque(a) => out.push(a),
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cex::dissect::{GoalShape, Hypothesis};
    use frontend::ast::{BaseType, BinOp};

    fn var(v: &str) -> Expr {
        Expr::Var(v.to_string())
    }
    fn ctor(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Constructor { name: name.to_string(), args }
    }
    fn call(f: &str, args: Vec<Expr>) -> Expr {
        Expr::Call { func: f.to_string(), args }
    }
    fn eq(l: Expr, r: Expr) -> Expr {
        Expr::BinOp { op: BinOp::Eq, left: Box::new(l), right: Box::new(r) }
    }
    fn parts(path_conds: Vec<Expr>, assumptions: Vec<Expr>, hypotheses: Vec<Expr>) -> VcParts {
        VcParts {
            skolems: vec![("v".to_string(), BaseType::Custom("D".to_string()))],
            path_conds,
            hypotheses: hypotheses.into_iter().map(|fact| Hypothesis { gate: None, fact }).collect(),
            goal: GoalShape { assumptions, core: Core::Bool(var("p")) },
        }
    }

    #[test]
    fn pattern_equalities_nest_and_a_bare_variable_has_no_shape() {
        let p = parts(
            vec![eq(var("v"), ctor("D::Node", vec![var("h"), var("t")])), eq(var("t"), ctor("D::Node", vec![var("h2"), var("t2")]))],
            vec![],
            vec![],
        );
        let s = Shapes::from_goal(&p);
        assert_eq!(s.shape_of(&var("v")), Some(&ctor("D::Node", vec![var("h"), var("t")])));
        assert_eq!(s.expand(&var("v")), ctor("D::Node", vec![var("h"), ctor("D::Node", vec![var("h2"), var("t2")])]));
        assert_eq!(s.shape_of(&var("t2")), None);
        assert_eq!(s.expand(&var("t2")), var("t2"));
    }

    #[test]
    fn assumptions_hypotheses_and_literals_give_shapes() {
        let p = parts(
            vec![],
            vec![eq(var("w"), ctor("D::Leaf", vec![]))],
            vec![eq(ctor("D::Node", vec![var("a"), var("b")]), call("f", vec![var("a")]))],
        );
        let s = Shapes::from_goal(&p);
        assert_eq!(s.shape_of(&var("w")), Some(&ctor("D::Leaf", vec![])));
        assert_eq!(s.shape_of(&call("f", vec![var("a")])), Some(&ctor("D::Node", vec![var("a"), var("b")])));
        let literal = ctor("D::Node", vec![var("x"), ctor("D::Leaf", vec![])]);
        assert_eq!(s.shape_of(&literal), Some(&literal));
    }

    #[test]
    fn derived_shapes_expand_inside_applications_and_never_override() {
        let p = parts(vec![eq(var("v"), ctor("D::Node", vec![var("h"), var("t")]))], vec![], vec![]);
        let mut s = Shapes::from_goal(&p);
        // len(v) = S(len(t)): recorded as written, found after expansion too.
        s.add_derived(call("len", vec![var("v")]), ctor("P::S", vec![call("len", vec![var("t")])]));
        assert_eq!(
            s.expand(&call("sub", vec![call("len", vec![var("v")]), var("i")])),
            call("sub", vec![ctor("P::S", vec![call("len", vec![var("t")])]), var("i")])
        );
        // a non-constructor result is not a shape
        s.add_derived(call("rev", vec![var("v")]), call("app", vec![call("rev", vec![var("t")]), var("h")]));
        assert_eq!(s.shape_of(&call("rev", vec![var("v")])), None);
        // the first shape wins
        s.add_derived(call("len", vec![var("v")]), ctor("P::Z", vec![]));
        assert_eq!(s.shape_of(&call("len", vec![var("v")])), Some(&ctor("P::S", vec![call("len", vec![var("t")])])));
    }

    #[test]
    fn a_cyclic_derived_shape_cannot_loop() {
        let p = parts(vec![], vec![], vec![]);
        let mut s = Shapes::from_goal(&p);
        s.add_derived(call("f", vec![var("x")]), ctor("P::S", vec![call("f", vec![var("x")])]));
        let e = s.expand(&call("f", vec![var("x")]));
        // finite: a tower of at most EXPAND_FUEL successors
        let mut depth = 0;
        let mut cur = &e;
        while let Expr::Constructor { args, .. } = cur {
            depth += 1;
            cur = &args[0];
        }
        assert!(depth <= EXPAND_FUEL);
    }
}
