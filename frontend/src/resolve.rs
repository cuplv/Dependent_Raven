//! frontend/src/resolve.rs
//! Pattern type resolution pass (패턴 타입 결정 패스)
//!
//! [ENG] Role: fills the `arg_types` field of every `Pattern::Constructor` in an
//! expression, by looking up the constructor's field sorts in the datatype table
//! (`Program.datatypes`). The parser cannot do this itself: `convert_pattern` is a
//! pure syn→AST mapping that sees one item at a time, while the datatype defining
//! a constructor (e.g. `enum List`) is registered by a *different* item. The first
//! moment the full datatype table and a parsed body coexist is registration time,
//! so this pass runs once in `api.rs::register_val`, right after `convert_expr`
//! and BEFORE the body is stored in `Program.functions` or type-checked.
//!
//! No type inference is needed: a constructor's field sorts depend only on the
//! constructor's name (`Cons` is always `[Elem, List]`), never on the context in
//! which the pattern appears. Only bare `Ident`/`Wildcard` patterns depend on the
//! scrutinee's type, and the consumers already receive that locally.
//!
//! Interactions / invariant: after this pass, every `Pattern::Constructor` in the
//! program carries `Some(arg_types)` consistent with `Program.datatypes`. The
//! downstream consumers — `typechecking.rs::bind_pattern_vars` (frontend binders)
//! and `smt/mod.rs::extract_pat_binders` (backend axiom binders) — read the field
//! instead of looking up the table themselves, and must treat `None` as a missing
//! pass (panic). Unknown constructors and arity mismatches are reported here, at
//! registration time, instead of surfacing later as ill-sorted SMT asserts.
//!
//! [KOR] 역할: 표현식 안의 모든 `Pattern::Constructor`의 `arg_types` 필드를
//! 데이터타입 테이블(`Program.datatypes`)에서 조회한 필드 sort로 채웁니다.
//! 파서는 이를 할 수 없습니다: `convert_pattern`은 아이템 하나만 보는 순수
//! syn→AST 변환이고, 생성자를 정의하는 데이터타입(예: `enum List`)은 *다른*
//! 아이템에서 등록되기 때문입니다. 전체 테이블과 파싱된 본문이 처음으로 함께
//! 존재하는 시점이 등록 시점이므로, 이 패스는 `api.rs::register_val`에서
//! `convert_expr` 직후, 본문이 `Program.functions`에 저장되거나 타입 체킹되기
//! 전에 한 번 실행됩니다.
//!
//! 타입 추론은 필요 없습니다: 생성자의 필드 sort는 오직 생성자 이름에만 의존하고
//! (`Cons`는 항상 `[Elem, List]`), 패턴이 나타나는 문맥에는 의존하지 않습니다.
//!
//! 상호작용 / 불변식: 이 패스 이후 프로그램의 모든 `Pattern::Constructor`는
//! `Program.datatypes`와 일치하는 `Some(arg_types)`를 갖습니다. 소비자인
//! `typechecking.rs::bind_pattern_vars`(프론트엔드 바인더)와
//! `smt/mod.rs::extract_pat_binders`(백엔드 공리 바인더)는 테이블을 직접 조회하는
//! 대신 이 필드를 읽으며, `None`을 만나면 패스 누락으로 간주하고 panic해야 합니다.
//! 알 수 없는 생성자와 인자 개수 불일치는 나중에 잘못된 sort의 SMT assert로
//! 나타나는 대신, 여기 등록 시점에서 보고됩니다.

use std::collections::HashMap;
use crate::ast::{BaseType, Expr, Ident, Pattern};

/// [ENG] Entry point: walks `expr` and stamps every constructor pattern in it.
/// [KOR] 진입점: `expr`를 순회하며 안의 모든 생성자 패턴에 타입을 새깁니다.
pub fn resolve_pattern_types(
    expr: &mut Expr,
    datatypes: &HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>,
) {
    // A match on a tuple is first compiled into matches on single variables; the
    // result is then resolved like any other expression.
    let compiled = match expr {
        Expr::Match { expr: target, arms } => match &**target {
            Expr::Tuple(components) => Some(compile_tuple_match(components, arms, datatypes)),
            _ => None,
        },
        _ => None,
    };
    if let Some(nested) = compiled {
        *expr = nested;
    }

    match expr {
        Expr::Let { pat, bound_expr, body } => {
            resolve_in_pattern(pat, datatypes);
            resolve_pattern_types(bound_expr, datatypes);
            resolve_pattern_types(body, datatypes);
        }
        Expr::Match { expr: target, arms } => {
            resolve_pattern_types(target, datatypes);
            for (pat, arm_expr) in arms.iter_mut() {
                resolve_in_pattern(pat, datatypes);
                resolve_pattern_types(arm_expr, datatypes);
            }
            expand_catch_all_arms(arms, datatypes);
            reject_overlapping_arms(arms);
        }

        // 나머지 노드들은 자식만 순회 / Remaining nodes: just traverse children.
        Expr::Tuple(elems) => {
            for e in elems {
                resolve_pattern_types(e, datatypes);
            }
        }
        Expr::BinOp { left, right, .. } => {
            resolve_pattern_types(left, datatypes);
            resolve_pattern_types(right, datatypes);
        }
        Expr::UnOp { expr: inner, .. } => resolve_pattern_types(inner, datatypes),
        Expr::If { cond, then_expr, else_expr } => {
            resolve_pattern_types(cond, datatypes);
            resolve_pattern_types(then_expr, datatypes);
            resolve_pattern_types(else_expr, datatypes);
        }
        Expr::Call { args, .. } | Expr::Constructor { args, .. } | Expr::ApplyRel { args, .. } => {
            for a in args {
                resolve_pattern_types(a, datatypes);
            }
        }
        Expr::Forall { body, .. } | Expr::Exists { body, .. } => {
            resolve_pattern_types(body, datatypes);
        }
        Expr::Instantiate(inner) => resolve_pattern_types(inner, datatypes),
        Expr::ExistentialBindings(bindings) => {
            for (_, e) in bindings {
                resolve_pattern_types(e, datatypes);
            }
        }
        Expr::BoolConst(_) | Expr::Var(_) => {}
    }
}

/// [ENG] Compiles `match (a, b, ..) { rows }` into nested matches on the single
/// variables `a`, `b`, .. -- the only match form the checker and the backend
/// handle. Rows are tried in source order (Rust's first-match semantics), so rows
/// may overlap and a bare `_` row stands for "any tuple"; the matches produced
/// have one arm per constructor and are therefore disjoint by construction.
/// [KOR] 튜플에 대한 match를 단일 변수들에 대한 중첩 match로 컴파일합니다. 행은 소스
/// 순서대로 시도되므로(Rust의 first-match) 행들이 겹쳐도 됩니다. 만들어지는 match는
/// 생성자마다 arm이 하나라서 구성상 서로소입니다.
fn compile_tuple_match(
    components: &[Expr],
    arms: &[(Pattern, Expr)],
    datatypes: &HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>,
) -> Expr {
    let scrutinees: Vec<Ident> = components
        .iter()
        .map(|c| match c {
            Expr::Var(name) => name.clone(),
            other => panic!(
                "the components of a tuple match must be variables, got {:?}; \
                 bind it with `let` first",
                other
            ),
        })
        .collect();
    let rows: Vec<(Vec<Pattern>, Expr)> = arms
        .iter()
        .map(|(pat, body)| match pat {
            Pattern::Tuple(ps) if ps.len() == scrutinees.len() => (ps.clone(), body.clone()),
            Pattern::Wildcard => (vec![Pattern::Wildcard; scrutinees.len()], body.clone()),
            other => panic!(
                "a match on a {}-tuple needs {}-tuple patterns or `_`, got `{}`",
                scrutinees.len(), scrutinees.len(), render_pattern(other)
            ),
        })
        .collect();
    if rows.is_empty() {
        panic!("a tuple match needs at least one arm");
    }
    compile_rows(&scrutinees, rows, datatypes)
}

/// [ENG] One step of the decision tree: `rows[i].0[j]` is the pattern row `i` has
/// for `scrutinees[j]`. The first column is eliminated, either by binding (no row
/// tests it) or by a match on its constructors; with no columns left, the first
/// remaining row is the one Rust would have taken.
fn compile_rows(
    scrutinees: &[Ident],
    rows: Vec<(Vec<Pattern>, Expr)>,
    datatypes: &HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>,
) -> Expr {
    let Some((scrutinee, rest)) = scrutinees.split_first() else {
        return rows.into_iter().next().expect("checked non-empty by the caller").1;
    };

    // The datatype of this column, read off the first row that tests it.
    let tested = rows.iter().find_map(|(pats, _)| match &pats[0] {
        Pattern::Constructor { name, .. } => name.rsplit_once("::").map(|(e, _)| e.to_string()),
        _ => None,
    });
    let Some(enum_name) = tested else {
        let rows = rows
            .into_iter()
            .map(|(pats, body)| (pats[1..].to_vec(), bind(&pats[0], scrutinee, body)))
            .collect();
        return compile_rows(rest, rows, datatypes);
    };

    let variants = datatypes.get(&enum_name).unwrap_or_else(|| panic!(
        "Pattern resolution: unknown datatype '{}' in a tuple match", enum_name
    ));
    let arms = variants
        .iter()
        .map(|(variant, field_types)| {
            let name = format!("{}::{}", enum_name, variant);
            let fields: Vec<Ident> = field_types
                .iter()
                .map(|_| match crate::parser::name_nested_wildcards(Pattern::Wildcard) {
                    Pattern::Ident(fresh) => fresh,
                    _ => unreachable!("a wildcard is named by an identifier"),
                })
                .collect();
            // Rows that can still match once this column is known to be `name(..)`:
            // their sub-patterns become the columns for the fields.
            let sub_rows: Vec<(Vec<Pattern>, Expr)> = rows
                .iter()
                .filter_map(|(pats, body)| match &pats[0] {
                    Pattern::Constructor { name: n, args, .. } if *n == name => {
                        Some(([&args[..], &pats[1..]].concat(), body.clone()))
                    }
                    Pattern::Constructor { .. } => None,
                    irrefutable => Some((
                        [&vec![Pattern::Wildcard; fields.len()][..], &pats[1..]].concat(),
                        bind(irrefutable, scrutinee, body.clone()),
                    )),
                })
                .collect();
            if sub_rows.is_empty() {
                panic!("tuple match is not exhaustive: no row covers `{}`", name);
            }
            let columns = [&fields[..], rest].concat();
            let pattern = Pattern::Constructor {
                name,
                args: fields.into_iter().map(Pattern::Ident).collect(),
                arg_types: None,
            };
            (pattern, compile_rows(&columns, sub_rows, datatypes))
        })
        .collect();
    Expr::Match { expr: Box::new(Expr::Var(scrutinee.clone())), arms }
}

/// [ENG] A row's binder for a column becomes `let x = scrutinee` around its body;
/// a wildcard binds nothing.
fn bind(pat: &Pattern, scrutinee: &Ident, body: Expr) -> Expr {
    match pat {
        Pattern::Ident(x) => Expr::Let {
            pat: Pattern::Ident(x.clone()),
            bound_expr: Box::new(Expr::Var(scrutinee.clone())),
            body: Box::new(body),
        },
        Pattern::Wildcard => body,
        other => panic!("nested tuple pattern `{}` is not supported", render_pattern(other)),
    }
}

/// [ENG] Replaces every bare `_` arm by the patterns the arms BEFORE it leave
/// uncovered (Rust's first-match semantics), each carrying a copy of the arm's
/// body -- a `_` arm binds nothing, so the body needs no adjustment. The new arms
/// are disjoint from the earlier ones by construction, which is what the
/// unordered-cases encoding below requires. The datatype of the scrutinee is read
/// off the first constructor arm; a `_` arm with none before it is rejected.
/// [KOR] 맨 `_` arm을, 그 앞의 arm들이 덮지 못한 패턴들로 대체합니다(Rust의 first-match
/// 의미론). 각 패턴은 arm 본문의 사본을 가집니다. 새 arm들은 앞선 arm들과 구성상 서로소입니다.
fn expand_catch_all_arms(
    arms: &mut Vec<(Pattern, Expr)>,
    datatypes: &HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>,
) {
    let mut expanded: Vec<(Pattern, Expr)> = Vec::new();
    for (pat, body) in arms.drain(..) {
        if !matches!(pat, Pattern::Wildcard) {
            expanded.push((pat, body));
            continue;
        }
        let scrutinee_ty = expanded
            .iter()
            .find_map(|(p, _)| match p {
                Pattern::Constructor { name, .. } => name
                    .rsplit_once("::")
                    .map(|(enum_name, _)| BaseType::Custom(enum_name.to_string())),
                _ => None,
            })
            .unwrap_or_else(|| panic!(
                "a `_` match arm needs a constructor arm before it: it stands for the \
                 constructors the earlier arms leave uncovered"
            ));
        let mut uncovered = vec![Pattern::Wildcard];
        for (earlier, _) in &expanded {
            uncovered = uncovered
                .iter()
                .flat_map(|q| subtract(q, &scrutinee_ty, earlier, datatypes))
                .collect();
        }
        for q in uncovered {
            expanded.push((crate::parser::name_nested_wildcards(q), body.clone()));
        }
    }
    *arms = expanded;
}

/// [ENG] The patterns that match exactly the values `q` matches and `p` does not;
/// they are pairwise disjoint. `ty` is the sort at this position, needed to split
/// a wildcard into the constructors of its datatype.
fn subtract(
    q: &Pattern,
    ty: &BaseType,
    p: &Pattern,
    datatypes: &HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>,
) -> Vec<Pattern> {
    match (q, p) {
        (_, Pattern::Wildcard | Pattern::Ident(_)) => vec![],
        (Pattern::Wildcard | Pattern::Ident(_), Pattern::Constructor { .. }) => {
            let BaseType::Custom(enum_name) = ty else {
                panic!("constructor pattern `{}` at a position of sort {:?}", render_pattern(p), ty)
            };
            datatypes[enum_name]
                .iter()
                .flat_map(|(variant, field_types)| {
                    let split = Pattern::Constructor {
                        name: format!("{}::{}", enum_name, variant),
                        args: vec![Pattern::Wildcard; field_types.len()],
                        arg_types: Some(field_types.clone()),
                    };
                    subtract(&split, ty, p, datatypes)
                })
                .collect()
        }
        (
            Pattern::Constructor { name: q_name, args: q_args, arg_types },
            Pattern::Constructor { name: p_name, args: p_args, .. },
        ) => {
            if q_name != p_name {
                return vec![q.clone()];
            }
            // C(q1..qn) minus C(p1..pn): for each field i, the values that agree with
            // p on the fields before i, escape p at field i, and are free after it.
            let field_types = arg_types.as_ref().expect("stamped by resolve_in_pattern");
            let mut out = Vec::new();
            let mut agreed: Vec<Pattern> = Vec::new();
            for i in 0..q_args.len() {
                for r in subtract(&q_args[i], &field_types[i], &p_args[i], datatypes) {
                    let mut args = agreed.clone();
                    args.push(r);
                    args.extend_from_slice(&q_args[i + 1..]);
                    out.push(Pattern::Constructor {
                        name: q_name.clone(),
                        args,
                        arg_types: arg_types.clone(),
                    });
                }
                match intersect(&q_args[i], &p_args[i]) {
                    Some(m) => agreed.push(m),
                    None => break,
                }
            }
            out
        }
        _ => panic!("a `_` match arm is not supported together with tuple patterns"),
    }
}

/// [ENG] A pattern matching exactly the values both `q` and `p` match, with every
/// binder erased to a wildcard; `None` if no value matches both.
fn intersect(q: &Pattern, p: &Pattern) -> Option<Pattern> {
    match (q, p) {
        (Pattern::Wildcard | Pattern::Ident(_), Pattern::Wildcard | Pattern::Ident(_)) => {
            Some(Pattern::Wildcard)
        }
        (Pattern::Wildcard | Pattern::Ident(_), c @ Pattern::Constructor { .. })
        | (c @ Pattern::Constructor { .. }, Pattern::Wildcard | Pattern::Ident(_)) => intersect(c, c),
        (
            Pattern::Constructor { name: q_name, args: q_args, arg_types },
            Pattern::Constructor { name: p_name, args: p_args, .. },
        ) => {
            if q_name != p_name {
                return None;
            }
            let args = q_args
                .iter()
                .zip(p_args)
                .map(|(x, y)| intersect(x, y))
                .collect::<Option<Vec<_>>>()?;
            Some(Pattern::Constructor { name: q_name.clone(), args, arg_types: arg_types.clone() })
        }
        _ => panic!("a `_` match arm is not supported together with tuple patterns"),
    }
}

/// [ENG] Match arms are encoded as UNORDERED cases (one VC per arm in proofs, one
/// definitional equation per arm in function bodies); nothing records that the
/// earlier arms did not match. Rust's first-match semantics is therefore only
/// reproduced when the arms are pairwise disjoint. Two overlapping arms in a
/// function body yield two equations for the same value, which is inconsistent
/// whenever their right-hand sides differ. Reject rather than mis-encode.
/// [KOR] match arm은 순서 없는 경우들로 인코딩되므로(증명: arm마다 VC, 함수 본문: arm마다
/// 정의 등식), 이전 arm이 매치되지 않았다는 사실은 기록되지 않습니다. 따라서 arm들이 쌍별로
/// 서로소일 때만 Rust의 first-match 의미론이 재현됩니다. 겹치는 arm은 거부합니다.
fn reject_overlapping_arms(arms: &[(Pattern, Expr)]) {
    for i in 0..arms.len() {
        for j in (i + 1)..arms.len() {
            if !patterns_disjoint(&arms[i].0, &arms[j].0) {
                panic!(
                    "match arms {} (`{}`) and {} (`{}`) overlap; arms are encoded as unordered \
                     cases, so every pair must be disjoint -- spell out the constructors",
                    i + 1, render_pattern(&arms[i].0), j + 1, render_pattern(&arms[j].0)
                );
            }
        }
    }
}

/// [ENG] True iff no value can match both patterns. A wildcard or a variable
/// matches everything; two constructor patterns are disjoint iff their heads
/// differ or some corresponding pair of fields is disjoint; likewise for tuples.
fn patterns_disjoint(p: &Pattern, q: &Pattern) -> bool {
    match (p, q) {
        (Pattern::Wildcard, _) | (_, Pattern::Wildcard)
        | (Pattern::Ident(_), _) | (_, Pattern::Ident(_)) => false,
        (
            Pattern::Constructor { name: n1, args: a1, .. },
            Pattern::Constructor { name: n2, args: a2, .. },
        ) => n1 != n2 || a1.iter().zip(a2).any(|(x, y)| patterns_disjoint(x, y)),
        (Pattern::Tuple(a1), Pattern::Tuple(a2)) => {
            a1.iter().zip(a2).any(|(x, y)| patterns_disjoint(x, y))
        }
        // A constructor against a tuple cannot both match one value.
        _ => true,
    }
}

fn render_pattern(pat: &Pattern) -> String {
    match pat {
        Pattern::Wildcard => "_".to_string(),
        Pattern::Ident(name) => name.clone(),
        Pattern::Constructor { name, args, .. } if args.is_empty() => name.clone(),
        Pattern::Constructor { name, args, .. } => format!(
            "{}({})",
            name,
            args.iter().map(render_pattern).collect::<Vec<_>>().join(", ")
        ),
        Pattern::Tuple(args) => format!(
            "({})",
            args.iter().map(render_pattern).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// [ENG] Stamps one pattern (and its sub-patterns) with constructor field sorts.
/// [KOR] 패턴 하나(와 그 하위 패턴)에 생성자 필드 sort를 새깁니다.
fn resolve_in_pattern(
    pat: &mut Pattern,
    datatypes: &HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>,
) {
    match pat {
        Pattern::Wildcard | Pattern::Ident(_) => {}
        Pattern::Tuple(ps) => {
            for p in ps {
                resolve_in_pattern(p, datatypes);
            }
        }
        Pattern::Constructor { name, args, arg_types } => {
            // 이름 형식은 파서가 만든 "Enum::Variant" / Parser produces "Enum::Variant".
            let (enum_name, variant_name) = name
                .rsplit_once("::")
                .unwrap_or_else(|| panic!(
                    "Pattern resolution: constructor pattern '{}' is not qualified as 'Enum::Variant'",
                    name
                ));

            let variants = datatypes.get(enum_name).unwrap_or_else(|| panic!(
                "Pattern resolution: unknown datatype '{}' in pattern '{}' (is the enum defined before this function?)",
                enum_name, name
            ));

            let (_, field_types) = variants
                .iter()
                .find(|(v, _)| v == variant_name)
                .unwrap_or_else(|| panic!(
                    "Pattern resolution: datatype '{}' has no constructor '{}'",
                    enum_name, variant_name
                ));

            if args.len() != field_types.len() {
                panic!(
                    "Pattern resolution: constructor '{}' expects {} argument(s), pattern has {}",
                    name, field_types.len(), args.len()
                );
            }

            *arg_types = Some(field_types.clone());

            // 중첩 생성자 패턴은 자신의 이름으로 다시 조회됨 / Nested constructor
            // patterns resolve via their own name lookup.
            for p in args {
                resolve_in_pattern(p, datatypes);
            }
        }
    }
}
