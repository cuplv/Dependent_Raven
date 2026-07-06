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
    match expr {
        Expr::Let { pat, bound_expr, body } => {
            resolve_in_pattern(pat, datatypes);
            resolve_pattern_types(bound_expr, datatypes);
            resolve_pattern_types(body, datatypes);
        }
        Expr::Match { expr: target, arms } => {
            resolve_pattern_types(target, datatypes);
            for (pat, arm_expr) in arms {
                resolve_in_pattern(pat, datatypes);
                resolve_pattern_types(arm_expr, datatypes);
            }
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
