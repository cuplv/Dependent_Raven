//! frontend/src/typechecking.rs
//! A simplified, unidirectional (bottom-up synthesis) type checker focused on F* style proofs.

use std::collections::HashMap;
use crate::ast::*;
use crate::env::{TypeEnv, substitute_expr};

/// [KOR] 수식의 타입을 상향식(Synthesis)으로 추론하며, 필요한 경우 서브타이핑 검사를 통해 VC를 생성합니다.
/// [ENG] Infers the type of an expression bottom-up (Synthesis), generating VCs via subtyping checks when necessary.
pub fn synthesize_expr(
    env: &mut TypeEnv,
    expr: &Expr,
    global_specs: &HashMap<Ident, FunctionDef>,
    vcs: &mut Vec<SubGoal>,
) -> Type {
    match expr {
        // [T-CONST]: 상수
        // 상수의 정체성을 보존하는 Singleton Refinement Type 반환 (예: {v: Bool | v == true})
        Expr::BoolConst(b) => {
            Type::Refined(RefinedType {
                bound_var: "v".to_string(),
                base: BaseType::Bool,
                predicate: Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(Expr::Var("v".to_string())),
                    right: Box::new(Expr::BoolConst(*b)),
                },
            })
        }

        // [T-VAR]: 변수
        // 환경(env)이나 global_specs에서 변수 타입을 찾고, BaseType이면 Singleton Refinement 적용
        Expr::Var(name) => {
            let var_type = if let Some(t) = env.lookup_var(name) {
                t.clone()
            } else if let Some(def) = global_specs.get(name) {
                def.signature.clone()
            } else if name.contains("::") {
                // 데이터 생성자 (예: Nat::Z) Fallback
                let base_name = name.split("::").next().unwrap().to_string();
                Type::Base(BaseType::Custom(base_name))
            } else {
                panic!("Unbound identifier: {}", name);
            };

            match var_type {
                // 기본 타입일 경우에만 Singleton Refinement를 적용 (논문 Rule 1)
                // 예: x의 원래 타입이 Int 이면, {v: Int | v == x} 를 반환.
                Type::Base(b) | Type::Refined(RefinedType { base: b, .. }) => {
                    Type::Refined(RefinedType {
                        bound_var: "v".to_string(),
                        base: b,
                        predicate: Expr::BinOp {
                            op: BinOp::Eq,
                            left: Box::new(Expr::Var("v".to_string())),
                            right: Box::new(Expr::Var(name.clone())),
                        },
                    })
                }
                // 함수 타입 등은 보존하여 반환 (논문 Rule 2)
                _ => var_type,
            }
        }

        // [T-LET]: Let 바인딩 (let pat = bound_expr in body)
        // [KOR] 
        // 1. bound_expr의 타입을 추론합니다.
        // 2. 새로운 스코프를 열고 패턴 변수를 환경에 바인딩한 뒤 body의 타입을 추론합니다.
        // 3. 지역 변수 유출(Scope Leakage) 방지:
        //    body의 추론된 타입 안에 지역 변수(pat)가 남아있어 밖으로 유출되면 SMT 솔버가 "Unbound Variable" 에러를 냅니다.
        //    현재는 이를 막기 위해 정제 조건을 완전히 지워버리고 뼈대(BaseType)로 강등(Downgrading)시켜 반환합니다.
        // TODO(Enhancement): 추후 Catalyst 논문에서 제시한 존재 양화사(Existential Quantification)와 스콜렘화(Skolemization) 
        //                    기법을 도입하여, 정보 손실 없이 안전하게 타입을 밖으로 내보내는 방식으로 고도화해야 합니다.
        // [ENG]
        // 1. Infer the type of bound_expr.
        // 2. Open a new scope, bind pattern variables to the environment, and infer the type of the body.
        // 3. Prevention of Scope Leakage:
        //    If the inferred body type contains local variables (pat) and leaks outside, the SMT solver will throw an "Unbound Variable" error.
        //    Currently, to prevent this, we entirely drop the refinement predicate and downgrade to a BaseType before returning.
        // TODO(Enhancement): In the future, implement the Existential Quantification and Skolemization technique presented in the Catalyst paper 
        //                    to safely export types without information loss.
        Expr::Let { pat, bound_expr, body } => {
            // 1. bound_expr의 타입 추론
            let bound_type = synthesize_expr(env, bound_expr, global_specs, vcs);

            // 2. 스코프를 열고 변수 바인딩 후 body 타입 추론
            let body_type = env.with_scope(|inner_env| {
                bind_pattern_vars(inner_env, pat, &bound_type);
                synthesize_expr(inner_env, body, global_specs, vcs)
            });

            // 3. 변수 유출 방어를 위한 보수적 강등 (Conservative Downgrading)
            // 이상적으로는 body_type 내부에 pat 변수가 쓰였는지 검사해야 하지만,
            // 현재 증명 스크립트는 Unit만 반환하므로 무조건 강등해도 안전합니다.
            match body_type {
                Type::Refined(r) => Type::Base(r.base),
                other => other, // BaseType, Arrow, Lemma 등은 그대로 반환
            }
        }

        // [T-IF]: 제어 흐름 분기 (Synthesis with OR-Join Heuristic)
        // TODO(Fixme): 두 브랜치의 Refinement를 OR로 묶어 반환하는 임시방편(Heuristic)입니다.
        //              - 장점: 단방향(Synthesis) 추론 환경에서도 두 브랜치의 값 정보(Information) 손실을 막아줍니다.
        //              - 단점 1: if/match 문이 중첩될수록 OR(||) 조건이 기하급수적으로 늘어나 SMT 솔버를 폭파(Path Explosion)시킬 위험이 있습니다.
        //              - 단점 2: 반환 타입이 함수(Arrow)인 고차 함수의 경우 OR로 묶을 수 있는 문법이 없어 패닉이 발생합니다.
        //              - 궁극적인 해결책: Liquid Types 논문처럼 부모 노드에서 목표 타입(Expected Type)을 하향식으로 내려주는 
        //                Checking 모드를 부활시켜야 근본적인 해결이 가능합니다.
        Expr::If { cond, then_expr, else_expr } => {
            // 1. 조건식(cond) 추론 및 검증 (부울 타입이어야 함)
            let cond_type = synthesize_expr(env, cond, global_specs, vcs);
            let base_cond = match cond_type {
                Type::Base(b) | Type::Refined(RefinedType { base: b, .. }) => b,
                _ => panic!("Condition must be a base type (Bool)"),
            };
            if base_cond != BaseType::Bool {
                panic!("Condition of if-expression must be Bool");
            }

            // 2. 'then' 브랜치 추론 (환경에 cond == true 주입)
            let then_type = env.with_scope(|inner_env| {
                inner_env.add_path_condition((**cond).clone());
                synthesize_expr(inner_env, then_expr, global_specs, vcs)
            });

            // 3. 'else' 브랜치 추론 (환경에 cond == false 주입)
            let else_type = env.with_scope(|inner_env| {
                inner_env.add_path_condition(Expr::UnOp { op: UnOp::Not, expr: cond.clone() });
                synthesize_expr(inner_env, else_expr, global_specs, vcs)
            });

            // 4. BaseType 추출 및 비교 (Refinement 분리)
            // 임시 바운드 변수 이름 "v_if"를 기준으로 통일하여 술어(Predicate)를 추출합니다.
            let bound_name = "v_if".to_string();
            let (b_then, p_then) = extract_base_and_pred(&then_type, &bound_name);
            let (b_else, p_else) = extract_base_and_pred(&else_type, &bound_name);

            if b_then != b_else {
                panic!("Type mismatch in IF branches: {:?} vs {:?}", b_then, b_else);
            }

            // 5. OR로 합친 거대한 Refinement 생성
            // {v_if: B | (cond && p_then) || (!cond && p_else)}
            let joined_predicate = Expr::BinOp {
                op: BinOp::Or,
                left: Box::new(Expr::BinOp {
                    op: BinOp::And,
                    left: cond.clone(),
                    right: Box::new(p_then),
                }),
                right: Box::new(Expr::BinOp {
                    op: BinOp::And,
                    left: Box::new(Expr::UnOp { op: UnOp::Not, expr: cond.clone() }),
                    right: Box::new(p_else),
                }),
            };

            Type::Refined(RefinedType {
                bound_var: bound_name,
                base: b_then,
                predicate: joined_predicate,
            })
        }

        // [T-MATCH]: 패턴 매칭
        // Checking 모드 전용으로 이동되었으므로 상향식 추론에서는 에러 처리합니다.
        Expr::Match { .. } => {
            unimplemented!("T-MATCH should be handled in check_expr (Checking Mode) when expected type is available.")
        }

        // =========================================================================
        // [T-APP / T-REC] Rule: Function / Lemma Application (The Core of Induction)
        // =========================================================================
        Expr::Call { func, args } => {
            // -----------------------------------------------------------------
            // PREMISE 1: \Gamma \vdash f : (x:\tau_{in}) \to \tau_{out}
            // -----------------------------------------------------------------
            // [KOR] 호출 대상인 함수의 시그니처를 환경(env)이나 전역 스펙(global_specs)에서 찾습니다.
            // [ENG] Look up the signature of the target function from the environment or global specs.
            let mut current_sig = if let Some(t) = env.lookup_var(func) {
                t.clone()
            } else if let Some(def) = global_specs.get(func) {
                def.signature.clone()
            } else {
                panic!("Unbound function or lemma: {}", func);
            };

            // -----------------------------------------------------------------
            // PREMISE 2: \Gamma \vdash e : \tau_{in}
            // -----------------------------------------------------------------
            // [KOR] 인자(args)를 하나씩 순회하며 함수가 요구하는 타입/조건을 만족하는지 검사합니다.
            // [ENG] Iterate through each argument, checking if it satisfies the function's required type/conditions.
            for arg in args {
                if let Type::Arrow(fun_type) = current_sig {
                    // [KOR] 1. 넘겨받은 실제 인자의 타입을 상향식으로 추론합니다. (e.g., e : \tau_{actual})
                    // [ENG] 1. Synthesize the type of the actual argument bottom-up.
                    let arg_type = synthesize_expr(env, arg, global_specs, vcs);

                    // [KOR] 2. 실제 인자의 타입이 함수가 요구하는 파라미터 타입(사전 조건 포함)의 서브타입인지 검사합니다.
                    //       이 과정에서 인자가 제약 조건을 만족하지 않으면 SMT 솔버가 실패할 VC가 생성됩니다.
                    //       (\Gamma \vdash \tau_{actual} <: \tau_{in})
                    // [ENG] 2. Check if the actual argument type is a subtype of the expected parameter type (including preconditions).
                    //       If the argument doesn't satisfy the constraints, a VC that fails in the SMT solver will be generated.
                    generate_subtyping_vc(env, &arg_type, &fun_type.param_type, vcs);

                    // -----------------------------------------------------------------
                    // CONSEQUENCE (Partial): [e/x]\tau_{out}
                    // -----------------------------------------------------------------
                    // [KOR] 3. 함수의 나머지 시그니처(반환 타입)에 있는 형식 매개변수(Formal Parameter)를
                    //       실제 인자(Actual Argument) 수식으로 완벽히 치환(Substitution)합니다! 🌟
                    //       이 치환을 통해 귀납 가정(Induction Hypothesis)이 현재 문맥에 맞게 구체화됩니다.
                    // [ENG] 3. Substitute the formal parameter in the rest of the signature (return type)
                    //       with the actual argument expression! 🌟
                    //       Through this substitution, the Induction Hypothesis is instantiated to fit the current context.
                    current_sig = substitute_expr_in_type(&fun_type.ret_type, &fun_type.param_name, arg);
                } else {
                    panic!("Too many arguments provided for function {}", func);
                }
            }

            // -----------------------------------------------------------------
            // CONSEQUENCE (Final): \Gamma \vdash f(e) : [e/x]\tau_{out}
            // -----------------------------------------------------------------
            // [KOR] 모든 인자를 성공적으로 치환하고 남은 최종 타입이 이 함수 호출의 결과 타입(귀납 가정)입니다.
            // [ENG] The final type remaining after substituting all arguments is the return type of this call (the Induction Hypothesis).
            current_sig
        }

        // =========================================================================
        // [T-CONSTRUCT] Rule: Data Constructor
        // =========================================================================
        Expr::Constructor { name, args } => {
            // [KOR] 데이터 생성자의 인자들을 체킹하여 내부에 숨겨진 VC를 생성하게 합니다.
            // [ENG] Check the arguments of the data constructor to generate any hidden VCs inside.
            for arg in args {
                synthesize_expr(env, arg, global_specs, vcs);
            }
            
            // [KOR] 생성자는 그 자체로 해당 데이터 타입을 반환합니다. (예: Nat::S -> Nat)
            // [ENG] A constructor itself returns its corresponding data type. (e.g., Nat::S -> Nat)
            let base_name = name.split("::").next().unwrap().to_string();
            Type::Base(BaseType::Custom(base_name))
        }

        Expr::Tuple(elems) => {
            // [KOR] 각 요소의 타입을 추론하여 BaseType::Tuple로 묶어 반환합니다. 빈 튜플은 Unit 반환.
            let mut base_types = Vec::new();
            for e in elems {
                let ty = synthesize_expr(env, e, global_specs, vcs);
                let (b, _) = extract_base_and_pred(&ty, "tmp");
                base_types.push(b);
            }
            if base_types.is_empty() {
                Type::Base(BaseType::Unit)
            } else {
                Type::Base(BaseType::Tuple(base_types))
            }
        }

        // [T-INSTANTIATE]: 수동 인스턴스화 (Manual Instantiation for CEGQI)
        Expr::Instantiate(inner) => {
            // [ENG] 1. Synthesize the inner ground term to ensure it is well-typed.
            let _ = synthesize_expr(env, inner, global_specs, vcs);
            
            // [ENG] 2. Following CEGQI, we collect instantiation axioms into a scoped list
            //          instead of binding them to the local path condition.
            env.add_instantiation(*inner.clone());
            
            // [ENG] 3. Return Unit type as it acts purely as a logical hint for the backend.
            Type::Base(BaseType::Unit)
        }

        Expr::BinOp { .. } | Expr::UnOp { .. } | Expr::Forall { .. } | Expr::Exists { .. } | Expr::ApplyRel { .. } | Expr::ExistentialBindings(_) => {
            unimplemented!("T-LOGIC not implemented")
        }
    }
}

// ============================================================================
// ⬇️ Checking Mode (하향식 타입 검사)
// ============================================================================

/// [KOR] 주어진 목표 타입(expected)을 바탕으로 수식을 하향식으로 검사합니다.
///       - Catalyst 논문의 방식대로, 목표 타입이 미리 주어졌다고 가정하고(Checking) VC만 생성합니다.
///       - 반환값이 없으므로(void), 정보 손실이나 꼼수(OR-Join 등) 없이 깔끔하게 처리됩니다.
/// [ENG] Checks an expression top-down against a given expected type.
///       - Follows the Catalyst paper's approach, assuming the expected type is provided (Checking) and only generating VCs.
///       - Since there is no return value (void), it avoids information loss and heuristics like OR-Joins.
pub fn check_expr(
    env: &mut TypeEnv,
    expr: &Expr,
    expected: &Type,
    global_specs: &HashMap<Ident, FunctionDef>,
    vcs: &mut Vec<SubGoal>,
) {
    match expr {
        // ---------------------------------------------------------
        // [T-LET]: Let 바인딩 (Checking Mode)
        // ---------------------------------------------------------
        // [KOR] 블록 안에 instantiate! 나 다른 let 구문이 섞여 있을 때,
        //       마지막 구문이 Match라면 Checking Mode를 그대로 유지하며 내려보내야 합니다.
        // [ENG] When a block contains `instantiate!` or other `let` bindings,
        //       we must propagate the Expected type down to the body so that `Match` can use it.
        Expr::Let { pat, bound_expr, body } => {
            let bound_type = synthesize_expr(env, bound_expr, global_specs, vcs);
            env.with_scope(|inner_env| {
                bind_pattern_vars(inner_env, pat, &bound_type);
                check_expr(inner_env, body, expected, global_specs, vcs);
            });
        }

        // ---------------------------------------------------------
        // [T-MATCH]: 패턴 매칭 (Catalyst Checking Rule)
        // ---------------------------------------------------------
        // [KOR] 논문 규칙 분석:
        //       Premise 1: target(v)의 타입을 상향식으로 추론합니다. (Γ ⊢ v : intlist)
        //       Premise 3: 각 arm(Cons, Nil)마다 스코프를 열고, 바인딩(Γ_c) 및 경로 조건([v/ν]φ_c)을 주입합니다.
        //       Premise 4: 각 arm의 본문(e_i)이 목표 타입(τ, expected)의 서브타입이 되는지 하향식으로 검사합니다.
        //       Consequence: 모든 브랜치가 통과하면, 이 match 구문 전체가 τ 타입을 반환한다고 "증명"됩니다!
        // [ENG] Paper Rule Analysis:
        //       Premise 1: Synthesize the type of the target (v). (Γ ⊢ v : intlist)
        //       Premise 3: For each arm (Cons, Nil), open a scope, inject bindings (Γ_c) and path conditions ([v/ν]φ_c).
        //       Premise 4: Check if each arm's body (e_i) satisfies the expected target type (τ) top-down.
        //       Consequence: If all branches pass, the entire match expression is proven to safely return type τ!
        Expr::Match { expr: target, arms } => {
            // [Premise 1]: 매칭 대상(target)의 타입을 상향식(Synthesis)으로 알아냅니다.
            let target_type = synthesize_expr(env, target, global_specs, vcs);

            for (pat, arm_expr) in arms {
                // 스코프를 열어 각 브랜치만의 격리된 임시 환경(Local Context)을 만듭니다.
                env.with_scope(|inner_env| {
                    
                    // [Premise 3 (Part 1)]: 변수 바인딩 (Γ_c, Γ_n 구축)
                    // 패턴 내의 변수들(예: x, y)을 target_type 기반으로 추론하여 환경에 등록합니다.
                    bind_pattern_vars(inner_env, pat, &target_type);
                    
                    // [Premise 3 (Part 2)]: 경로 조건 주입 ([v/ν]φ_c, [v/ν]φ_n)
                    // "현재 매칭된 타겟 변수는 이 패턴(생성자)과 완벽히 일치한다"는 수학적 사실을 SMT 솔버에게 알려줍니다.
                    // 이 조건이 있어야 귀납법(Inductive Step)이나 분기별 특수성을 SMT가 증명할 수 있습니다.
                    let eq_expr = build_pattern_eq_expr(target, pat);
                    inner_env.add_path_condition(eq_expr);
                    
                    // [Premise 4]: 브랜치 본문 검사 (Γ, Γ_c ⊢ e_1 : τ)
                    // 여기서 '재귀'가 발생합니다! 
                    // arm_expr 안의 논리식이나 수식들이 expected 타입의 서브타입인지 검사(check_expr)하며, 
                    // 이 과정에서 최종적으로 서브타이핑 룰에 의해 VC가 생성(vcs.push)됩니다.
                    check_expr(inner_env, arm_expr, expected, global_specs, vcs);
                });
            }
        }
        
        // Checking fallback: 만약 Match 등 명시적인 하향식 제어 구문이 아니라면,
        // 상향식으로 추론(Synthesize)한 뒤, 그 결과가 expected의 서브타입인지 검사합니다.
        // [KOR] Subtyping 규칙의 진입점입니다!
        // [ENG] This is the entry point for Subtyping rules!
        _ => {
            let inferred = synthesize_expr(env, expr, global_specs, vcs);
            generate_subtyping_vc(env, &inferred, expected, vcs);
        }
    }
}

// ============================================================================
// ⚖️ Subtyping Logic (VC Generation Core)
// ============================================================================

/// [KOR] inferred 타입이 expected 타입을 만족하는지 검사하여, 논리적 함의(Implication)를 VC로 뱉어냅니다.
/// [ENG] Checks if `inferred` is a subtype of `expected`, generating logical implication VCs.
pub fn generate_subtyping_vc(
    env: &mut TypeEnv,
    inferred: &Type,
    expected: &Type,
    vcs: &mut Vec<SubGoal>
) {
    match (inferred, expected) {
        // =========================================================================
        // [DEC-<:-BASE] Rule: Base / Refined Type Subtyping
        // =========================================================================
        // [KOR] 기본 타입(Base) 및 정제 타입(Refined) 간의 서브타이핑을 처리합니다.
        //       Type::Base는 내부적으로 조건이 'true'인 정제 타입으로 간주됩니다.
        // [ENG] Handles subtyping between Base and Refined types. 
        //       Type::Base is internally treated as a Refined type with a 'true' predicate.
        (Type::Base(_), Type::Base(_)) |
        (Type::Base(_), Type::Refined(_)) |
        (Type::Refined(_), Type::Base(_)) |
        (Type::Refined(_), Type::Refined(_)) => {
            
            // [KOR] 두 타입의 바운드 변수(\nu) 이름을 통일하기 위한 임시 변수명입니다.
            // [ENG] A temporary variable name to unify the bound variables (\nu) of both types.
            let common_var = "v_sub".to_string();

            // [KOR] 뼈대 타입(BaseType B)과 내부 논리식(Predicate e_1, e_2)을 추출합니다.
            // [ENG] Extract the BaseType (B) and internal logical predicate (e_1, e_2).
            let (base_inf, pred_inf) = extract_base_and_pred(inferred, &common_var);
            let (base_exp, pred_exp) = extract_base_and_pred(expected, &common_var);

            // [KOR] 서브타이핑의 대전제: 두 타입의 뼈대(BaseType)는 완벽히 동일해야 합니다.
            // [ENG] Prerequisite of subtyping: The underlying BaseTypes must be exactly identical.
            if base_inf != base_exp {
                panic!("Base type mismatch in subtyping: {:?} <: {:?}", base_inf, base_exp);
            }

            // [KOR] 스코프를 열어 임시 변수와 가정들을 안전하게 격리합니다.
            // [ENG] Open a new scope to safely isolate the temporary variable and assumptions.
            env.with_scope(|inner_env| {
                
                // -----------------------------------------------------------------
                // PREMISE PART 1: [[\Gamma]] \wedge [[e_1]]
                // -----------------------------------------------------------------
                // [KOR] Inferred 타입의 바운드 변수를 환경에 추가하고 (forall 생성을 위해), 
                //       조건(pred_inf, 즉 e_1)을 참이라고 가정(Assume)하여 환경(Gamma)에 덧붙입니다.
                // [ENG] Insert the bound variable of the Inferred type to the env (for 'forall' generation),
                //       and assume the Inferred condition (pred_inf, i.e., e_1) is true, appending it to Gamma.
                inner_env.insert_var(common_var.clone(), Type::Base(base_inf));
                inner_env.add_path_condition(pred_inf);
                
                // -----------------------------------------------------------------
                // PREMISE PART 2: \Rightarrow [[e_2]]
                // -----------------------------------------------------------------
                // [KOR] 누적된 환경(Gamma \wedge e_1)을 바탕으로 Expected 타입의 조건(pred_exp, 즉 e_2)을 
                //       도출(Imply)하는 최종 Verification Condition(VC)을 생성합니다.
                //       build_implication 내부에서 \forall v_sub. (Gamma \wedge e_1 \Rightarrow e_2) 가 완성됩니다.
                // [ENG] Based on the accumulated environment (Gamma \wedge e_1), generate the final 
                //       Verification Condition (VC) that implies the Expected condition (pred_exp, i.e., e_2).
                //       Inside `build_implication`, the form \forall v_sub. (Gamma \wedge e_1 \Rightarrow e_2) is completed.
                let vc = inner_env.build_implication(pred_exp);
                
                // -----------------------------------------------------------------
                // CONSEQUENCE: \Gamma \vdash \{\nu:B \mid e_1\} <: \{\nu:B \mid e_2\}
                // -----------------------------------------------------------------
                // [KOR] 현재 스코프에서 유효한 힌트들을 모아, 최종 VC와 함께 SubGoal로 포장하여 배열에 넣습니다.
                // [ENG] Collect active instantiations for this specific scope and package them into a SubGoal.
                let active_insts = inner_env.get_active_instantiations();
                vcs.push(SubGoal {
                    property: vc,
                    instantiations: active_insts,
                });
            });
        }

        // =========================================================================
        // [SUBT-ARROW] / [DEC-<:-FUN] Rule: Function (Arrow) Type Subtyping
        // =========================================================================
        (Type::Arrow(f_inf), Type::Arrow(f_exp)) => {
            // -----------------------------------------------------------------
            // PREMISE 1: \Gamma \vdash T'_x <: T_x (Contravariance of Arguments)
            // -----------------------------------------------------------------
            // [KOR] 인자 타입은 반공변성(Contravariance)을 가집니다.
            //       즉, Expected(목표) 인자 타입이 Inferred(실제) 인자 타입의 서브타입이어야 합니다.
            //       (예상되는 함수가 더 좁은 인자를 요구하더라도, 실제 함수가 더 넓은 범위를 수용하면 안전함)
            // [ENG] Argument types are contravariant.
            //       The Expected argument type must be a subtype of the Inferred argument type.
            //       (It is safe if the actual function accepts a wider range than the expected function demands)
            generate_subtyping_vc(env, &f_exp.param_type, &f_inf.param_type, vcs);

            // -----------------------------------------------------------------
            // PREMISE 2: \Gamma; x:T'_x \vdash T <: T' (Covariance of Return Types)
            // -----------------------------------------------------------------
            // [KOR] 반환 타입은 공변성(Covariance)을 가집니다.
            //       단, "인자가 Expected의 규칙(T'_x)을 따른다"고 가정한 새로운 스코프 안에서,
            //       Inferred의 반환 타입이 Expected의 반환 타입의 서브타입이어야 합니다.
            // [ENG] Return types are covariant.
            //       However, in a new scope assuming "the argument follows the Expected rule (T'_x)",
            //       the Inferred return type must be a subtype of the Expected return type.
            env.with_scope(|inner_env| {
                // [KOR] 1. Expected의 파라미터(x: T'_x)를 환경에 등록합니다.
                //       호출자가 Expected의 제약에 맞게 올바른 인자를 넣었다고 가정하는 것입니다.
                // [ENG] 1. Register the Expected parameter (x: T'_x) into the environment.
                //       This assumes the caller provided a valid argument satisfying the Expected constraints.
                inner_env.insert_var(f_exp.param_name.clone(), *f_exp.param_type.clone());

                // [KOR] 2. Inferred 반환 타입의 파라미터(f_inf.param_name)를 
                //       Expected의 파라미터명(f_exp.param_name)으로 치환하여 통일합니다.
                // [ENG] 2. Substitute the parameter name in the Inferred return type (f_inf.param_name)
                //       with the Expected parameter name (f_exp.param_name) to unify them.
                let unified_inf_ret = substitute_expr_in_type(
                    &f_inf.ret_type, 
                    &f_inf.param_name, 
                    &Expr::Var(f_exp.param_name.clone())
                );
                
                // [KOR] 3. 통일된 반환 타입 간의 서브타이핑(T <: T')을 재귀적으로 검사합니다.
                //       여기서 생성되는 VC가 바로 "함수 반환값이 조건을 만족하는가"에 대한 증명입니다.
                // [ENG] 3. Recursively check subtyping between the unified return types (T <: T').
                //       The VC generated here proves whether the function return value satisfies the condition.
                generate_subtyping_vc(inner_env, &unified_inf_ret, &f_exp.ret_type, vcs);
            });
            
            // -----------------------------------------------------------------
            // CONSEQUENCE: \Gamma \vdash (x:T_x) \to T <: (x:T'_x) \to T'
            // -----------------------------------------------------------------
            // [KOR] 위의 두 Premise(인자 서브타이핑, 반환값 서브타이핑)에서 생성된 VC들이 모두 vcs에 담깁니다.
            //       이 VC들이 SMT 솔버에서 모두 Valid로 판명되면, 최종적으로 함수 서브타이핑이 성립합니다.
            // [ENG] All VCs generated from the two Premises (argument and return subtyping) are accumulated in `vcs`.
            //       If the SMT solver proves all these VCs are Valid, the function subtyping holds ultimately.
        }

        _ => {
            panic!("Invalid subtyping comparison between incompatible type structures: {:?} <: {:?}", inferred, expected);
        }
    }
}

// ============================================================================
// 🛠️ Helpers (To be migrated from old typecheck.rs)
// ============================================================================

/// [KOR] 패턴(Pattern) 매칭으로 추출된 변수들을 타입 환경(TypeEnv)에 등록합니다.
///       - T-MATCH 규칙에서 각 arm 내부를 검사할 때, 귀납법으로 쪼개진 하위 구조(예: `x_prime`)를 환경에 넣을 때 사용됩니다.
///       - T-LET 규칙에서 바운드된 변수를 본문 검사 전에 환경에 넣을 때 사용됩니다.
/// [ENG] Registers variables extracted from a Pattern into the TypeEnv.
///       - Used in T-MATCH to bind destructured subterms (e.g., `x_prime`) before typechecking an arm.
///       - Used in T-LET to bind the local variable before typechecking the body.
pub fn bind_pattern_vars(env: &mut TypeEnv, pat: &Pattern, ty: &Type) {
    match (pat, ty) {
        (Pattern::Wildcard, _) => {} // 무시
        (Pattern::Ident(name), _) => env.insert_var(name.clone(), ty.clone()), // 변수 바인딩
        (Pattern::Tuple(ps), Type::Base(BaseType::Tuple(ts))) | (Pattern::Tuple(ps), Type::Refined(RefinedType { base: BaseType::Tuple(ts), .. })) => {
            for (p, t_base) in ps.iter().zip(ts.iter()) {
                bind_pattern_vars(env, p, &Type::Base(t_base.clone()));
            }
        }
        (Pattern::Constructor(_, args), _) => {
            // 생성자 패턴의 인자들(예: S(x_prime)의 x_prime)은 
            // 원래 데이터 타입과 동일한 BaseType을 가진다고 가정 (단순화)
            let base = match ty {
                Type::Base(b) | Type::Refined(RefinedType { base: b, .. }) => b.clone(),
                _ => panic!("Cannot bind constructor pattern to complex type"),
            };
            for arg_pat in args {
                bind_pattern_vars(env, arg_pat, &Type::Base(base.clone()));
            }
        }
        _ => panic!("Binding mismatch: {:?} vs {:?}", pat, ty),
    }
}

/// [KOR] 패턴 매칭의 대상(Target)과 패턴(Pattern) 사이의 동치(==) 논리식을 만듭니다.
///       - T-MATCH 규칙의 핵심입니다! 이 함수가 만든 수식(예: `target == Nat::S(x_prime)`)이 
///         환경의 경로 조건(Path Condition)으로 주입되어 SMT 솔버가 현재 브랜치의 문맥을 알게 합니다.
/// [ENG] Builds an equality (==) logical expression between a match Target and a Pattern.
///       - Crucial for T-MATCH! The resulting expression (e.g., `target == Nat::S(x_prime)`) 
///         is injected into the environment's Path Conditions, letting the SMT solver know the context of the branch.
pub fn build_pattern_eq_expr(target: &Expr, pat: &Pattern) -> Expr {
    Expr::BinOp {
        op: BinOp::Eq,
        left: Box::new(target.clone()),
        right: Box::new(pattern_to_expr(pat)),
    }
}

/// [KOR] 패턴(Pattern) 구조체를 논리식(Expr) 구조체로 변환합니다. (build_pattern_eq_expr 헬퍼용)
/// [ENG] Converts a Pattern struct into an Expr struct. (Helper for build_pattern_eq_expr)
pub fn pattern_to_expr(pat: &Pattern) -> Expr {
    match pat {
        Pattern::Wildcard => unimplemented!("Wildcard is not allowed currently"), 
        Pattern::Ident(name) => Expr::Var(name.clone()),
        Pattern::Constructor(name, args) => {
            Expr::Constructor { name: name.clone(), args: args.iter().map(pattern_to_expr).collect() }
        }
        Pattern::Tuple(elems) => Expr::Tuple(elems.iter().map(pattern_to_expr).collect()),
    }
}

/// [KOR] 타입(Type)에서 뼈대(BaseType)와 정제 조건(Predicate Expr)을 분리해 냅니다.
///       - T-IF와 T-MATCH에서 여러 브랜치의 조건을 OR로 합치기 위해 사용됩니다.
///       - 반환되는 Predicate는 인자로 받은 `target_var_name`으로 바운드 변수가 치환된 상태로 나옵니다.
/// [ENG] Extracts the BaseType and the Predicate Expr from a Type.
///       - Used in T-IF and T-MATCH to join conditions from multiple branches with OR.
///       - The returned Predicate has its bound variable substituted with `target_var_name`.
pub fn extract_base_and_pred(ty: &Type, target_var_name: &str) -> (BaseType, Expr) {
    match ty {
        Type::Base(b) => {
            // BaseType만 있는 경우 조건은 무조건 참(True)
            (b.clone(), Expr::BoolConst(true))
        }
        Type::Refined(r) => {
            // 바운드 변수 이름을 통일하기 위해 치환
            let sub_pred = substitute_expr(
                &r.predicate, 
                &r.bound_var, 
                &Expr::Var(target_var_name.to_string())
            );
            (r.base.clone(), sub_pred)
        }
        _ => panic!("Expected Base or Refined type, but got a complex type (Arrow or Lemma)"),
    }
}

/// [KOR] 타입 내의 바운드 변수 이름을 실제 수식으로 치환합니다.
/// [ENG] Substitutes a bound variable name in a type with an actual expression.
pub fn substitute_expr_in_type(ty: &Type, target_var: &str, replacement: &Expr) -> Type {
    match ty {
        Type::Base(b) => Type::Base(b.clone()),
        Type::Refined(r) => {
            if r.bound_var == target_var { 
                ty.clone() 
            } else {
                Type::Refined(RefinedType {
                    bound_var: r.bound_var.clone(),
                    base: r.base.clone(),
                    predicate: substitute_expr(&r.predicate, &target_var.to_string(), replacement),
                })
            }
        }
        Type::Arrow(f) => {
            if f.param_name == target_var { 
                ty.clone() 
            } else {
                Type::Arrow(FunType {
                    param_name: f.param_name.clone(),
                    param_type: Box::new(substitute_expr_in_type(&f.param_type, target_var, replacement)),
                    ret_type: Box::new(substitute_expr_in_type(&f.ret_type, target_var, replacement)),
                })
            }
        }
    }
}
