//! backend/src/smt/builder.rs
//! AST(Expr)를 easy_smt::SExpr로 변환하는 변환기

use easy_smt::{Context, SExpr};
use frontend::ast::{Expr, BinOp, UnOp, BaseType, Ident};

/// [KOR] 식별자에 들어있는 `::`를 SMT-LIB2가 파싱할 수 있는 안전한 `__`로 치환합니다.
pub fn sanitize_id(id: &str) -> String {
    id.replace("::", "__")
}

/// [KOR] BaseType을 SMT 상의 Sort 문자열로 렌더링합니다.
/// [ENG] Renders a BaseType to an SMT Sort string.
pub fn render_sort(b: &BaseType) -> String {
    match b {
        BaseType::Bool => "Bool".to_string(),
        BaseType::Unit => "Unit".to_string(),
        BaseType::Custom(name) => format!("UI_{}", sanitize_id(name)),
        BaseType::Tuple(ts) => {
            let mut s = "TUPLE".to_string();
            for t in ts {
                s.push_str(&format!("__{}", render_sort(t)));
            }
            s
        }
    }
}

/// [KOR] Expr 트리를 순회하며 easy_smt::SExpr로 변환합니다.
///       이미 NNF와 RelAbs를 거쳤으므로 매우 단순한 매핑만 수행합니다.
/// [ENG] Traverses the Expr tree and converts it to easy_smt::SExpr.
///       Since it already passed NNF and RelAbs, it performs a very simple mapping.
pub fn expr_to_smt(ctx: &mut Context, expr: &Expr) -> std::io::Result<SExpr> {
    match expr {
        // 1. 논리 상수
        Expr::BoolConst(true) => Ok(ctx.true_()),
        Expr::BoolConst(false) => Ok(ctx.false_()),

        // 2. 변수 (식별자)
        Expr::Var(name) => Ok(ctx.atom(sanitize_id(name))),

        // 3. 단항 연산자
        Expr::UnOp { op: UnOp::Not, expr: inner } => {
            let inner_smt = expr_to_smt(ctx, inner)?;
            Ok(ctx.not(inner_smt))
        }

        // 4. 이항 연산자
        Expr::BinOp { op, left, right } => {
            let l_smt = expr_to_smt(ctx, left)?;
            let r_smt = expr_to_smt(ctx, right)?;
            match op {
                BinOp::And => Ok(ctx.and(l_smt, r_smt)),
                BinOp::Or => Ok(ctx.or(l_smt, r_smt)),
                BinOp::Implies => Ok(ctx.list(vec![ctx.atom("=>"), l_smt, r_smt])),
                BinOp::Eq => Ok(ctx.eq(l_smt, r_smt)),
                BinOp::Neq => Ok(ctx.distinct(l_smt, r_smt)),
            }
        }

        // 5. 양화사 (Quantifiers)
        Expr::Forall { binders, body } => {
            let q_sig: Vec<_> = binders.iter().map(|(name, base_type)| {
                (sanitize_id(name), ctx.atom(render_sort(base_type)))
            }).collect();
            let body_smt = expr_to_smt(ctx, body)?;
            if binders.is_empty() {
                Ok(body_smt)
            } else {
                Ok(ctx.forall(q_sig, body_smt))
            }
        }
        Expr::Exists { binders, body } => {
            let q_sig: Vec<_> = binders.iter().map(|(name, base_type)| {
                (sanitize_id(name), ctx.atom(render_sort(base_type)))
            }).collect();
            let body_smt = expr_to_smt(ctx, body)?;
            if binders.is_empty() {
                Ok(body_smt)
            } else {
                Ok(ctx.exists(q_sig, body_smt))
            }
        }

        // 6. 관계식 적용 (ApplyRel) - 핵심!
        Expr::ApplyRel { relation, args } => {
            let mut smt_args = Vec::new();
            smt_args.push(ctx.atom(&sanitize_id(relation))); // 관계식(함수) 이름이 리스트의 첫 번째 원소
            for arg in args {
                smt_args.push(expr_to_smt(ctx, arg)?);
            }
            // (relation arg1 arg2 ...) 형태로 변환
            Ok(ctx.list(smt_args))
        }

        // 7. 파이프라인에서 제거되었어야 할 노드들
        Expr::Call { .. } | Expr::Constructor { .. } => {
            panic!("Call and Constructor should have been replaced by ApplyRel during RelAbs phase");
        }
        Expr::Let { .. } => {
            panic!("Let bindings should have been flattened out or transformed by RelAbs");
        }
        Expr::If { .. } => {
            panic!("If expressions should have been flattened or not exist in final formulas");
        }
        Expr::Match { .. } | Expr::Tuple(_) => {
            panic!("Match and Tuple expressions are not supported in SMT backend");
        }
    }
}
