//! backend/src/anf.rs
//! A-Normal Form (ANF) 변환기
//! 
//! [KOR] 중첩된 함수 호출을 평탄화(Flattening)하여, SMT 솔버가 이해하기 쉬운
//!       순수한 관계식(Relation)으로 치환할 수 있도록 준비하는 단계입니다.
//!       예: `P(add(a, sub(b, c)))` ➡️ `let v1 = sub(b, c) in let v2 = add(a, v1) in P(v2)`
//! 
//! [ENG] Flattens nested function calls so they can be easily replaced
//!       with pure relations for the SMT solver.

use frontend::ast::{Expr, Ident, Pattern, BinOp, UnOp, BaseType};

/// 고유한 임시 변수 이름을 생성하기 위한 상태 저장소
pub struct NameGenerator {
    counter: usize,
}

impl NameGenerator {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    /// 새로운 임시 변수 이름 생성 (예: "anf_0", "anf_1")
    pub fn fresh(&mut self) -> Ident {
        let name = format!("anf_{}", self.counter);
        self.counter += 1;
        name
    }
}

/// 수식을 ANF로 변환합니다.
/// 
/// [KOR] 수식 트리(Expr)를 순회하며 복잡한 하위 수식(함수 호출 등)을 
///       새로운 임시 변수(`v`)에 할당하는 `Let` 바인딩 껍데기들의 리스트와,
///       그 껍데기들 안에 들어갈 핵심 알맹이 수식을 반환합니다.
pub fn transform_expr(expr: &Expr, gen: &mut NameGenerator) -> Expr {
    let (bindings, core_expr) = flatten(expr, gen);
    
    // 추출된 바인딩들을 `let v1 = e1 in let v2 = e2 in ... core_expr` 형태로 조립
    build_let_chain(bindings, core_expr)
}

/// (바인딩 리스트, 알맹이 수식) 쌍을 나타내는 타입
type AnfResult = (Vec<(Ident, Expr)>, Expr);

/// 수식을 평탄화하여 바인딩 목록과 알맹이로 분리합니다.
fn flatten(expr: &Expr, gen: &mut NameGenerator) -> AnfResult {
    match expr {
        // 1. 이미 평탄한 기본 노드들 (변환 필요 없음)
        Expr::BoolConst(_) | Expr::Var(_) => {
            (vec![], expr.clone())
        }

        // 2. 튜플 (내부 요소들을 각각 평탄화)
        Expr::Tuple(elems) => {
            let mut all_bindings = vec![];
            let mut new_elems = vec![];
            for e in elems {
                let (mut bindings, core) = flatten(e, gen);
                all_bindings.append(&mut bindings);
                new_elems.push(core);
            }
            (all_bindings, Expr::Tuple(new_elems))
        }

        // 3. 단항 연산자
        Expr::UnOp { op: UnOp::Not, expr: inner } => {
            // [KOR] 논리 부정은 불리언(Boolean) 수준의 연산이므로 내부 바인딩을 위로 끌어올리지 않고 지역적으로 묶습니다.
            //       이를 통해 불필요한 양화사 스코프 확장에 의한 Sort Cycle을 방지합니다.
            let flat_inner = transform_expr(inner, gen);
            (vec![], Expr::UnOp {
                op: UnOp::Not,
                expr: Box::new(flat_inner),
            })
        }

        // 4. 이항 연산자
        Expr::BinOp { op, left, right } => {
            match op {
                // [KOR] 동치 연산자(Eq, Neq)는 값을 비교하므로, 양화사(Forall/Exists)가 비교 연산 안으로 들어가면
                //       SMT 문법 에러가 발생합니다. 따라서 반드시 바인딩을 연산자 위로 끌어올려야 합니다.
                BinOp::Eq | BinOp::Neq => {
                    let (mut l_bindings, l_core) = flatten(left, gen);
                    let (mut r_bindings, r_core) = flatten(right, gen);
                    l_bindings.append(&mut r_bindings);
                    (l_bindings, Expr::BinOp {
                        op: op.clone(),
                        left: Box::new(l_core),
                        right: Box::new(r_core),
                    })
                }
                // [KOR] 논리 연산자(And, Or, Implies)는 불리언(Boolean) 연산이므로 양화사를 포함할 수 있습니다.
                //       바인딩을 끌어올리지 않고 지역적으로 묶어 양화사 스코프를 최소화합니다. (Sort Cycle 방지)
                _ => {
                    let flat_left = transform_expr(left, gen);
                    let flat_right = transform_expr(right, gen);
                    (vec![], Expr::BinOp {
                        op: op.clone(),
                        left: Box::new(flat_left),
                        right: Box::new(flat_right),
                    })
                }
            }
        }

        // 5. 🌟 핵심: 일반 함수 호출 (Call) 🌟
        // 함수 호출은 SMT에서 관계식으로 치환될 운명이므로, 반드시 그 결과를 변수에 담아야 합니다.
        Expr::Call { func, args } => {
            let mut all_bindings = vec![];
            let mut new_args = vec![];
            
            // 먼저 인자들을 평탄화합니다 (f(g(x)) 에서 g(x)를 빼내는 작업)
            for arg in args {
                let (mut bindings, core) = flatten(arg, gen);
                all_bindings.append(&mut bindings);
                new_args.push(core);
            }

            // 평탄화된 인자를 가진 새로운 Call 노드 생성
            let flat_call = Expr::Call {
                func: func.clone(),
                args: new_args,
            };

            // 이 Call 노드 자체도 임시 변수(`v`)에 할당합니다!
            let fresh_var = gen.fresh();
            all_bindings.push((fresh_var.clone(), flat_call));

            // 알맹이는 방금 만든 임시 변수(`v`)가 됩니다.
            (all_bindings, Expr::Var(fresh_var))
        }

        // 6. 데이터 타입 생성자 (Constructor)
        // [KOR] 생성자 또한 SMT 솔버에서는 관계식(Relation)으로 치환되어야 하므로,
        //       일반 함수 호출과 마찬가지로 반드시 임시 변수에 할당해야 합니다.
        //       단, 인자가 0개인 생성자(예: `Nat::Z`)는 상수(Constant) 취급하여 평탄화하지 않습니다!
        Expr::Constructor { name, args } => {
            if args.is_empty() {
                // 상수는 임시 변수에 할당할 필요가 없음
                (vec![], expr.clone())
            } else {
                let mut all_bindings = vec![];
                let mut new_args = vec![];
                for arg in args {
                    let (mut bindings, core) = flatten(arg, gen);
                    all_bindings.append(&mut bindings);
                    new_args.push(core);
                }
                
                let flat_cons = Expr::Constructor {
                    name: name.clone(),
                    args: new_args,
                };

                let fresh_var = gen.fresh();
                all_bindings.push((fresh_var.clone(), flat_cons));

                (all_bindings, Expr::Var(fresh_var))
            }
        }

        // 7. 조건문 (If)
        Expr::If { cond, then_expr, else_expr } => {
            // 조건식은 밖으로 빼냅니다.
            let (bindings, cond_core) = flatten(cond, gen);
            
            // 브랜치 내부는 각자 독립적으로 ANF 변환(조립까지 완료)해야 합니다.
            // (브랜치 내부에서 생긴 변수가 바깥으로 새어나가면 안 되기 때문입니다.)
            let flat_then = transform_expr(then_expr, gen);
            let flat_else = transform_expr(else_expr, gen);

            (bindings, Expr::If {
                cond: Box::new(cond_core),
                then_expr: Box::new(flat_then),
                else_expr: Box::new(flat_else),
            })
        }

        // 8. 기존에 사용자가 작성한 Let 바인딩
        Expr::Let { pat, bound_expr, body } => {
            let (mut bindings, bound_core) = flatten(bound_expr, gen);
            
            // 원래 Let의 패턴과 묶인 값을 그대로 바인딩 리스트에 추가
            if let Pattern::Ident(var_name) = pat {
                bindings.push((var_name.clone(), bound_core));
            } else {
                // 튜플 언패킹 같은 복잡한 패턴은 일단 패스 (현재는 단순 변수 바인딩만 처리)
                panic!("Complex patterns in Let are not fully supported in ANF yet");
            }

            let (mut body_bindings, body_core) = flatten(body, gen);
            bindings.append(&mut body_bindings);

            (bindings, body_core)
        }

        // 9. 양화사 (Forall / Exists)
        // 내부 바디를 완전히 독립적으로 ANF 조립하여 반환
        Expr::Forall { binders, body } => {
            let flat_body = transform_expr(body, gen);
            (vec![], Expr::Forall {
                binders: binders.clone(),
                body: Box::new(flat_body),
            })
        }
        Expr::Exists { binders, body } => {
            let flat_body = transform_expr(body, gen);
            (vec![], Expr::Exists {
                binders: binders.clone(),
                body: Box::new(flat_body),
            })
        }

        // 10. 수동 인스턴스화 (Manual Instantiation)
        Expr::Instantiate(inner) => {
            // [KOR] 내부 수식을 평탄화하여 함수 호출 바인딩들(bindings)을 끄집어냅니다.
            //       기존의 Let 체인(Forall 긍정 극성)과 달리, 이 바인딩들은 반드시 존재해야 하는(Exists)
            //       강제 공리로 사용되므로 특수한 ExistentialBindings 노드로 감싸서 반환합니다.
            // [ENG] Flatten the inner expression to extract function call bindings.
            //       Unlike normal Let chains (which become Forall), these bindings MUST exist (Exists),
            //       so we wrap them in a special ExistentialBindings node.
            let (bindings, _core) = flatten(inner, gen);
            (vec![], Expr::ExistentialBindings(bindings))
        }

        Expr::ExistentialBindings(_) => {
            unreachable!("ExistentialBindings should not exist before ANF")
        }

        // Match와 ApplyRel은 보통 이 단계 이전에 없거나, Eval에서 정리된다고 가정
        _ => unimplemented!("ANF conversion for {:?}", expr),
    }
}

/// 추출된 바인딩 리스트를 중첩된 Let 구문으로 조립합니다.
fn build_let_chain(bindings: Vec<(Ident, Expr)>, core: Expr) -> Expr {
    let mut current_expr = core;

    // 바인딩 리스트를 역순으로 순회하며 안쪽부터 밖으로 Let으로 감쌉니다.
    for (var_name, bound_expr) in bindings.into_iter().rev() {
        current_expr = Expr::Let {
            pat: Pattern::Ident(var_name),
            bound_expr: Box::new(bound_expr),
            body: Box::new(current_expr),
        };
    }

    current_expr
}
