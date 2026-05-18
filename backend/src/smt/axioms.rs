//! backend/src/smt/axioms.rs
//! SMT 솔버를 위한 필수 공리(Axioms) 자동 생성기
//! 생성자(Constructor)와 함수(Function)가 수학적으로 올바르게 동작하도록
//! 함수성(Functionality), 단사성(Injectivity), 분리성(Disjointness) 공리를 Expr 형태로 생성합니다.

use frontend::ast::{Expr, BinOp, UnOp, BaseType, FunctionDef, Ident};

/// [KOR] 관계식에 사용할 고유 변수 이름을 생성하는 헬퍼 함수
/// [ENG] Helper function to generate unique variable names for relations
fn var_name(prefix: &str, idx: usize) -> Ident {
    format!("{}_{}", prefix, idx)
}

/// [KOR] Functionality Axiom (함수성 공리) 생성
///       모든 함수와 생성자는 SMT에서 관계식(Relation)으로 치환되므로, 
///       "같은 입력이 주어지면 항상 같은 결과가 나온다"는 성질을 주입해야 합니다.
///       ∀ x, r1, r2. (R(x, r1) ∧ R(x, r2)) ⟹ (r1 = r2)
/// [ENG] Generates Functionality Axiom.
///       Since all functions and constructors are relations in SMT, we must enforce
///       that "the same inputs always produce the same output".
pub fn functionality_axiom(rel_name: &str, input_types: &[BaseType], output_type: &BaseType) -> Expr {
    let mut binders = Vec::new();
    let mut args_for_rel1 = Vec::new();
    let mut args_for_rel2 = Vec::new();

    // 1. 입력 변수들 바인딩 (x_0, x_1, ...)
    for (i, ty) in input_types.iter().enumerate() {
        let v = var_name("in", i);
        binders.push((v.clone(), ty.clone()));
        args_for_rel1.push(Expr::Var(v.clone()));
        args_for_rel2.push(Expr::Var(v.clone()));
    }

    // 2. 두 개의 결과 변수 바인딩 (r1, r2)
    let r1 = "res_1".to_string();
    let r2 = "res_2".to_string();
    binders.push((r1.clone(), output_type.clone()));
    binders.push((r2.clone(), output_type.clone()));

    args_for_rel1.push(Expr::Var(r1.clone()));
    args_for_rel2.push(Expr::Var(r2.clone()));

    // 3. R(x, r1) ∧ R(x, r2)
    let rel1 = Expr::ApplyRel { relation: rel_name.to_string(), args: args_for_rel1 };
    let rel2 = Expr::ApplyRel { relation: rel_name.to_string(), args: args_for_rel2 };
    let condition = Expr::BinOp { op: BinOp::And, left: Box::new(rel1), right: Box::new(rel2) };

    // 4. r1 = r2
    let conclusion = Expr::BinOp { op: BinOp::Eq, left: Box::new(Expr::Var(r1)), right: Box::new(Expr::Var(r2)) };

    // 5. ∀ x, r1, r2. condition ⟹ conclusion
    Expr::Forall {
        binders,
        body: Box::new(Expr::BinOp {
            op: BinOp::Implies,
            left: Box::new(condition),
            right: Box::new(conclusion),
        })
    }
}

/// [KOR] Injectivity Axiom (단사성 공리) 생성
///       생성자(Constructor)의 핵심 성질입니다. 
///       "생성자로 감싼 결과가 같다면, 그 안의 알맹이(인자)들도 무조건 같아야 한다."
///       ∀ x, y, r. (C(x, r) ∧ C(y, r)) ⟹ (x = y)
/// [ENG] Generates Injectivity Axiom.
///       Crucial for constructors. "If the constructed results are equal, the inner arguments must be equal."
pub fn injectivity_axiom(cons_name: &str, input_types: &[BaseType], output_type: &BaseType) -> Expr {
    // 인자가 없는 생성자(예: Nat::Z)는 단사성을 증명할 알맹이가 없으므로 True 반환
    if input_types.is_empty() {
        return Expr::BoolConst(true);
    }

    let mut binders = Vec::new();
    let mut args_x = Vec::new();
    let mut args_y = Vec::new();
    let mut eq_checks = Vec::new();

    // 1. 알맹이 변수 세트 X와 Y 바인딩 (x_0, y_0, ...)
    for (i, ty) in input_types.iter().enumerate() {
        let vx = var_name("x", i);
        let vy = var_name("y", i);
        binders.push((vx.clone(), ty.clone()));
        binders.push((vy.clone(), ty.clone()));
        
        args_x.push(Expr::Var(vx.clone()));
        args_y.push(Expr::Var(vy.clone()));

        // 결론부: x_i == y_i
        eq_checks.push(Expr::BinOp {
            op: BinOp::Eq,
            left: Box::new(Expr::Var(vx)),
            right: Box::new(Expr::Var(vy)),
        });
    }

    // 2. 공통 결과 변수 바인딩 (r)
    let r = "res".to_string();
    binders.push((r.clone(), output_type.clone()));
    args_x.push(Expr::Var(r.clone()));
    args_y.push(Expr::Var(r.clone()));

    // 3. C(X, r) ∧ C(Y, r)
    let rel_x = Expr::ApplyRel { relation: cons_name.to_string(), args: args_x };
    let rel_y = Expr::ApplyRel { relation: cons_name.to_string(), args: args_y };
    let condition = Expr::BinOp { op: BinOp::And, left: Box::new(rel_x), right: Box::new(rel_y) };

    // 4. (x_0 = y_0) ∧ (x_1 = y_1) ∧ ...
    let mut conclusion = eq_checks.pop().unwrap();
    for eq in eq_checks.into_iter().rev() {
        conclusion = Expr::BinOp {
            op: BinOp::And,
            left: Box::new(eq),
            right: Box::new(conclusion),
        };
    }

    // 5. ∀ X, Y, r. condition ⟹ conclusion
    Expr::Forall {
        binders,
        body: Box::new(Expr::BinOp {
            op: BinOp::Implies,
            left: Box::new(condition),
            right: Box::new(conclusion),
        })
    }
}

/// [KOR] Disjointness Axiom (분리성 공리) 생성
///       서로 다른 두 생성자는 결코 같은 결과값을 낼 수 없습니다.
///       ∀ x, y, r. (C1(x, r) ∧ C2(y, r)) ⟹ False
/// [ENG] Generates Disjointness Axiom.
///       Two different constructors can never produce the same result.
pub fn disjointness_axiom(
    cons1_name: &str, inputs1: &[BaseType],
    cons2_name: &str, inputs2: &[BaseType],
    output_type: &BaseType
) -> Expr {
    let mut binders = Vec::new();
    let mut args1 = Vec::new();
    let mut args2 = Vec::new();

    // 1. C1의 인자 바인딩 (x_0, ...)
    for (i, ty) in inputs1.iter().enumerate() {
        let v = var_name("c1_in", i);
        binders.push((v.clone(), ty.clone()));
        args1.push(Expr::Var(v));
    }

    // 2. C2의 인자 바인딩 (y_0, ...)
    for (i, ty) in inputs2.iter().enumerate() {
        let v = var_name("c2_in", i);
        binders.push((v.clone(), ty.clone()));
        args2.push(Expr::Var(v));
    }

    // 3. 공통 결과 변수 (r)
    let r = "res".to_string();
    binders.push((r.clone(), output_type.clone()));
    args1.push(Expr::Var(r.clone()));
    args2.push(Expr::Var(r.clone()));

    // 4. C1(X, r) ∧ C2(Y, r) ⟹ False
    let rel1 = Expr::ApplyRel { relation: cons1_name.to_string(), args: args1 };
    let rel2 = Expr::ApplyRel { relation: cons2_name.to_string(), args: args2 };
    
    let condition = Expr::BinOp { op: BinOp::And, left: Box::new(rel1), right: Box::new(rel2) };

    Expr::Forall {
        binders,
        body: Box::new(Expr::BinOp {
            op: BinOp::Implies,
            left: Box::new(condition),
            right: Box::new(Expr::BoolConst(false)), // False를 함의 (즉, 절대 동시에 일어날 수 없음)
        })
    }
}
