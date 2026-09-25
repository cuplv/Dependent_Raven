//! backend/src/model
//! [KOR] 반례 모델(countermodel) 추출. `cex/`가 실패한 의무(obligation)를 소스
//!       어휘로 보여준다면, 이 모듈은 solver가 찾은 유한 모델을 같은 어휘로 보여줍니다.
//! [ENG] Countermodel extraction. Where `cex/` renders the failed obligation
//!       (branch, definitions, ledger, negated goal) in source vocabulary, this
//!       module renders the finite model the solver found in the same vocabulary:
//!       which element each variable is, what each application evaluates to,
//!       which elements no constructor produces (junk), and which unfolding is
//!       undefined. The representation below is solver-independent; each
//!       solver has its own directory that fills it (`z3/`; `cvc5/` later).

pub mod name;
pub mod print;
pub mod z3;

use std::collections::BTreeMap;

/// [ENG] An element of a sort's finite universe, by the solver's tag (e.g.
///       `UI_Nat!val!2`); for Bool-valued positions, `true` or `false`.
pub type Elem = String;

/// [ENG] A relation's interpretation, as solvers report it: the listed
///       argument tuples with their values, and the value of every other tuple.
///       An `else_value` of `true` means the relation holds everywhere except
///       where an entry says `false`; that is why the table is not simply "the
///       tuples on which it is true". An `else_value` of `None` means the solver
///       gave a formula instead of a constant there, and unlisted tuples are
///       unknown.
#[derive(Debug, Default, Clone)]
pub struct Table {
    pub entries: Vec<(Vec<Elem>, Elem)>,
    pub else_value: Option<Elem>,
}

impl Table {
    /// [ENG] The relation's value on `args`, if the table determines it.
    pub fn lookup(&self, args: &[Elem]) -> Option<&Elem> {
        self.entries
            .iter()
            .find(|(a, _)| a == args)
            .map(|(_, v)| v)
            .or(self.else_value.as_ref())
    }
}

/// [ENG] The signature of a relation as the query declares it:
///       `(declare-fun NAME (S1 .. Sn) Bool)` -> (`NAME`, [`S1`, .., `Sn`]).
///       Read from the query text, so it holds for any program and any solver.
pub fn declared_relations(query: &str) -> Vec<(String, Vec<String>)> {
    query
        .lines()
        .filter_map(|line| {
            let rest = line.trim().strip_prefix("(declare-fun ")?;
            let (name, rest) = rest.split_once(' ')?;
            let open = rest.find('(')?;
            let close = rest[open..].find(')')? + open;
            let columns = rest[open + 1..close].split_whitespace().map(str::to_string).collect();
            Some((name.to_string(), columns))
        })
        .collect()
}

/// [ENG] A finite model of one failed query.
#[derive(Debug, Default, Clone)]
pub struct Model {
    /// SMT sort name (`UI_Nat`) -> its universe.
    pub universes: BTreeMap<String, Vec<Elem>>,
    /// SMT constant name (`i`, `Nat__Z`) -> its element.
    pub consts: BTreeMap<String, Elem>,
    /// SMT relation name (`add_rel`, `Nat__S_rel`) -> its table.
    pub rels: BTreeMap<String, Table>,
}
