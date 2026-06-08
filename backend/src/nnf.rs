//! backend/src/nnf.rs
//! 부정 정규형 (Negation Normal Form, NNF) 변환기
//!
//! [KOR] 이 모듈은 수식 내의 모든 부정 기호(`!`)를 리프 노드(관계식, 동치 연산 등)로 밀어 넣습니다.
//!       Relational Abstraction(Task 6) 단계에서 함수 호출이 '긍정' 위치에 있는지 '부정' 위치에 있는지
//!       명확히 판별하기 위해 반드시 거쳐야 하는 필수 단계입니다.
//!
//! [ENG] This module pushes all negation operators (`!`) down to the leaf nodes (relations, equalities, etc.).
//!       It is a prerequisite for Relational Abstraction (Task 6) to clearly identify 
//!       whether a function call is in a 'positive' or 'negative' polarity.

use frontend::ast::{Expr, BinOp, UnOp, Ident, BaseType};

/// [KOR] 수식을 NNF로 변환합니다.
/// [ENG] Transforms an expression into Negation Normal Form.
pub fn transform_expr(expr: Expr) -> Expr {
    nnf(expr, false)
}

/// [KOR] 핵심 NNF 변환 함수. `is_negated`가 true이면 상위에서 `!` 기호가 내려오고 있음을 의미합니다.
/// [ENG] Core NNF transformation function. `is_negated` true means a `!` is being pushed down.
fn nnf(expr: Expr, is_negated: bool) -> Expr {
    match expr {
        // ---------------------------------------------------------
        // 1. 상수 및 변수 (Constants & Variables)
        // ---------------------------------------------------------
        Expr::BoolConst(b) => {
            // [KOR] !(true) -> false, !(false) -> true
            Expr::BoolConst(b ^ is_negated)
        }
        Expr::Var(x) => {
            if is_negated {
                Expr::UnOp { op: UnOp::Not, expr: Box::new(Expr::Var(x)) }
            } else {
                Expr::Var(x)
            }
        }

        // ---------------------------------------------------------
        // 2. 단항 연산 (Unary Operators)
        // ---------------------------------------------------------
        Expr::UnOp { op: UnOp::Not, expr: inner } => {
            // [KOR] !!A -> A (이중 부정 제거 / Double Negation Elimination)
            nnf(*inner, !is_negated)
        }

        // ---------------------------------------------------------
        // 3. 이항 연산 (Binary Operators - De Morgan & Implication)
        // ---------------------------------------------------------
        Expr::BinOp { op, left, right } => {
            match op {
                BinOp::And => {
                    if is_negated {
                        // [KOR] !(A && B) ➡️ !A || !B (드 모르간)
                        Expr::BinOp {
                            op: BinOp::Or,
                            left: Box::new(nnf(*left, true)),
                            right: Box::new(nnf(*right, true)),
                        }
                    } else {
                        Expr::BinOp {
                            op: BinOp::And,
                            left: Box::new(nnf(*left, false)),
                            right: Box::new(nnf(*right, false)),
                        }
                    }
                }
                BinOp::Or => {
                    if is_negated {
                        // [KOR] !(A || B) ➡️ !A && !B (드 모르간)
                        Expr::BinOp {
                            op: BinOp::And,
                            left: Box::new(nnf(*left, true)),
                            right: Box::new(nnf(*right, true)),
                        }
                    } else {
                        Expr::BinOp {
                            op: BinOp::Or,
                            left: Box::new(nnf(*left, false)),
                            right: Box::new(nnf(*right, false)),
                        }
                    }
                }
                BinOp::Implies => {
                    if is_negated {
                        // [KOR] !(A => B) ➡️ A && !B
                        Expr::BinOp {
                            op: BinOp::And,
                            left: Box::new(nnf(*left, false)),
                            right: Box::new(nnf(*right, true)),
                        }
                    } else {
                        // [KOR] A => B ➡️ !A || B
                        Expr::BinOp {
                            op: BinOp::Or,
                            left: Box::new(nnf(*left, true)),
                            right: Box::new(nnf(*right, false)),
                        }
                    }
                }
                BinOp::Eq => {
                    // [KOR] 동치 연산(==)의 피연산자가 논리식(Bool)인 경우:
                    //       A == B 는 (A => B) && (B => A) 와 같습니다.
                    //       양화사 극성(Polarity)을 정확히 추적하기 위해 이를 미리 전개하여 NNF를 적용합니다.
                    //       이는 EPR Sort Cycle 검사 시 양방향 의존성 간선을 자연스럽게 그릴 수 있게 해줍니다.
                    // [ENG] If operands of equality (==) are booleans (logical formulas):
                    //       A == B is equivalent to (A => B) && (B => A).
                    //       We expand this before applying NNF to correctly track quantifier polarity.
                    //       This naturally allows the EPR Sort Cycle checker to draw bidirectional dependency edges.
                    // 
                    //       참고: 현재 AST에서는 Eq가 논리식 비교인지 값 비교인지 구분이 안 되므로,
                    //       일단은 값 비교로 간주하고 부정만 안쪽으로 밀어넣습니다.
                    //       (만약 프론트엔드에서 논리식 동치 연산자 Iff를 별도로 두었다면 여기서 확장해야 함)
                    if is_negated {
                        // [KOR] !(A == B) ➡️ A != B
                        Expr::BinOp { op: BinOp::Neq, left: Box::new(nnf(*left, false)), right: Box::new(nnf(*right, false)) }
                    } else {
                        Expr::BinOp { op: BinOp::Eq, left: Box::new(nnf(*left, false)), right: Box::new(nnf(*right, false)) }
                    }
                }
                BinOp::Neq => {
                    if is_negated {
                        // [KOR] !(A != B) ➡️ A == B
                        Expr::BinOp { op: BinOp::Eq, left: Box::new(nnf(*left, false)), right: Box::new(nnf(*right, false)) }
                    } else {
                        Expr::BinOp { op: BinOp::Neq, left: Box::new(nnf(*left, false)), right: Box::new(nnf(*right, false)) }
                    }
                }
            }
        }

        // ---------------------------------------------------------
        // 4. 양화사 (Quantifiers - Inversion)
        // ---------------------------------------------------------
        Expr::Forall { binders, body } => {
            if is_negated {
                // [KOR] !(forall x. P) ➡️ exists x. !P
                Expr::Exists {
                    binders: binders.clone(),
                    body: Box::new(nnf(*body, true)),
                }
            } else {
                Expr::Forall {
                    binders: binders.clone(),
                    body: Box::new(nnf(*body, false)),
                }
            }
        }
        Expr::Exists { binders, body } => {
            if is_negated {
                // [KOR] !(exists x. P) ➡️ forall x. !P
                Expr::Forall {
                    binders: binders.clone(),
                    body: Box::new(nnf(*body, true)),
                }
            } else {
                Expr::Exists {
                    binders: binders.clone(),
                    body: Box::new(nnf(*body, false)),
                }
            }
        }

        // ---------------------------------------------------------
        // 5. 제어 흐름 및 바인딩 (Let, If)
        // ---------------------------------------------------------
        Expr::Let { pat, bound_expr, body } => {
            // [KOR] Let 바인딩은 구조를 유지하며 body만 NNF 처리합니다.
            // [ENG] Keep Let structure and apply NNF to the body.
            Expr::Let {
                pat,
                bound_expr, // 바운드되는 수식은 보통 ANF에서 Call이므로 그대로 둠
                body: Box::new(nnf(*body, is_negated)),
            }
        }
        Expr::If { cond, then_expr, else_expr } => {
            // [KOR] !(if C then T else E) ➡️ if C then !T else !E
            // [ENG] Push negation into both branches of an If.
            Expr::If {
                cond, // 조건문 자체는 긍정 위치로 고정
                then_expr: Box::new(nnf(*then_expr, is_negated)),
                else_expr: Box::new(nnf(*else_expr, is_negated)),
            }
        }

        // ---------------------------------------------------------
        // 6. 리프 노드 (Atoms: Call, Constructor, ApplyRel)
        // ---------------------------------------------------------
        Expr::Call { func, args } => {
            let core = Expr::Call { func, args };
            if is_negated { Expr::UnOp { op: UnOp::Not, expr: Box::new(core) } } else { core }
        }
        Expr::Constructor { name, args } => {
            let core = Expr::Constructor { name, args };
            if is_negated { Expr::UnOp { op: UnOp::Not, expr: Box::new(core) } } else { core }
        }
        Expr::ApplyRel { relation, args } => {
            let core = Expr::ApplyRel { relation, args };
            if is_negated { Expr::UnOp { op: UnOp::Not, expr: Box::new(core) } } else { core }
        }

        Expr::Tuple(elems) => Expr::Tuple(elems), // 보통 NNF에서 튜플은 논리식이 아니므로 그대로 둠
        
        Expr::Instantiate(_) => panic!("Instantiate should be eliminated by ANF"),
        
        Expr::ExistentialBindings(bindings) => {
            // [KOR] 내부 바인딩 수식들은 무조건 긍정(Positive) 극성으로 NNF를 통과해야 합니다.
            // [ENG] Inner binding expressions must pass through NNF with positive polarity.
            let new_bindings = bindings.into_iter()
                .map(|(id, e)| (id, nnf(e, false)))
                .collect();
            Expr::ExistentialBindings(new_bindings)
        }

        Expr::Match { .. } => panic!("Match should be eliminated by Eval before NNF"),
    }
}
