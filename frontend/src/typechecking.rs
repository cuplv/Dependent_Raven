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
        // [ENG]
        // 1. Infer the type of bound_expr.
        // 2. Open a new scope, bind pattern variables to the environment, and infer the type of the body.
        // 3. Prevention of Scope Leakage:
        //    If the inferred body type contains local variables (pat) and leaks outside, the SMT solver will throw an "Unbound Variable" error.
        //    Currently, to prevent this, we entirely drop the refinement predicate and downgrade to a BaseType before returning.
        // TODO(Enhancement): In the future, implement the Existential Quantification and Skolemization technique
        //                    to safely export types without information loss.
        Expr::Let { pat, bound_expr, body } => {
            let bound_type = synthesize_expr(env, bound_expr, global_specs, vcs);

            let body_type = env.with_scope(|inner_env| {
                bind_pattern_vars(inner_env, pat, &bound_type);
                synthesize_expr(inner_env, body, global_specs, vcs)
            });

            // [ENG] Substitution to prevent Scope Leakage:
            //       If the pattern is a simple identifier, substitute all occurrences of it 
            //       in the body's return type with the bound expression. 
            //       This mathematically pure approach (used by F*) prevents unbound variables 
            //       from leaking into the SMT query without losing refinement information.
            if let Pattern::Ident(var_name) = pat {
                substitute_expr_in_type(&body_type, var_name, bound_expr)
            } else {
                // [ENG] For complex patterns (like Tuples or Constructors), substitution is not trivially possible.
                //       Currently, we conservatively downgrade the inferred type to its BaseType to prevent scope leakage.
                //       TODO: In the future, implement "Existential Types (∃x:T1. T2)" as per the Catalyst paper.
                //             This will allow us to perfectly encapsulate and export the scope of complex patterns 
                //             without any information loss, by returning `Type::Exists(...)` instead of downgrading.
                match body_type {
                    Type::Refined(r) => Type::Base(r.base),
                    other => other,
                }
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

            // The callee's parameter names are only placeholders. If an actual
            // argument happens to be a variable with the same name as a LATER
            // parameter (e.g. calling `f(y, ..)` where f's second parameter is
            // also called `y`), plain textual substitution would conflate the
            // two: the first substitution writes `y` into the signature, and
            // the second one rewrites it again. Renaming every parameter to a
            // fresh name before substituting the actuals makes such collisions
            // impossible.
            current_sig = freshen_params(env, current_sig);

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
            
            // [KOR] 생성자 항은 자기 자신을 기록하는 singleton 타입 `{v | v == C(args)}`를
            //       받습니다(T-VAR가 변수에 하듯이). 그래야 이 항을 정제된 매개변수
            //       (requires)에 넘길 때 의무가 `v_sub == C(args)`를 알 수 있습니다.
            // [ENG] A constructor term gets the singleton type `{v | v == C(args)}`, as
            //       T-VAR does for variables, so an obligation on it (a `requires`
            //       parameter) knows that `v_sub == C(args)`.
            let base_name = name.split("::").next().unwrap().to_string();
            Type::Refined(RefinedType {
                bound_var: "v".to_string(),
                base: BaseType::Custom(base_name),
                predicate: Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(Expr::Var("v".to_string())),
                    right: Box::new(expr.clone()),
                },
            })
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

        // [T-LOGIC]: Boolean connectives and (dis)equality in PROGRAM position
        // (function bodies: `if` conditions, let-bound bools, Bool-returning
        // tails). Operands are synthesized so the calls inside them contribute
        // their own VCs; the result is the selfified Bool `{v: Bool | v == expr}`,
        // exactly as T-CONST and T-VAR do, so the connective reaches the backend
        // as a term. In SPEC position these nodes are never synthesized:
        // refinements are embedded as formulas directly.
        Expr::UnOp { op: UnOp::Not, expr: inner } => {
            let inner_ty = synthesize_expr(env, inner, global_specs, vcs);
            expect_base(&inner_ty, &BaseType::Bool, "operand of `!`");
            selfified_bool(expr.clone())
        }
        Expr::BinOp { op, left, right } => {
            let left_ty = synthesize_expr(env, left, global_specs, vcs);
            let right_ty = synthesize_expr(env, right, global_specs, vcs);
            match op {
                BinOp::And | BinOp::Or | BinOp::Implies => {
                    expect_base(&left_ty, &BaseType::Bool, "left operand of a logical connective");
                    expect_base(&right_ty, &BaseType::Bool, "right operand of a logical connective");
                }
                BinOp::Eq | BinOp::Neq => {
                    let (l, r) = (base_of(&left_ty), base_of(&right_ty));
                    if l.is_none() || l != r {
                        panic!(
                            "T-LOGIC: `==`/`!=` operands must have the same base sort, got {:?} and {:?}",
                            l, r
                        );
                    }
                }
            }
            selfified_bool(expr.clone())
        }

        Expr::Forall { .. } | Expr::Exists { .. } | Expr::ApplyRel { .. } | Expr::ExistentialBindings(_) => {
            unimplemented!("quantifiers are not allowed in program position (only inside specs)")
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
        // [KOR] 파서가 블록을 Let 체인으로 변환하므로, 블록의 모든 구문이 이 규칙을
        //       지나갑니다. 이 규칙의 역할은 각 구문이 알려주는 사실을 환경에 예치하여,
        //       같은 스코프에서 나중에 생성되는 검증 조건들이 그 사실을 쓸 수 있게
        //       하는 것입니다:
        //       1. 와일드카드 승격 — 값이 `_`에 묶이더라도 그 타입이 조건(refinement)을
        //          담고 있으면(예: Lemma 호출의 결과 타입은 사후조건을 담음) 내부용
        //          이름을 만들어 바인딩합니다. 이름이 있어야 to_logical_context가 그
        //          조건을 논리 문맥에 넣어줄 수 있기 때문입니다.
        //       2. 정의 방정식 — `이름 == 우변` 을 path condition으로 추가합니다. 이
        //          언어는 부수 효과가 없으므로 이 등식은 항상 참입니다. 이것이 있어야
        //          `let y = add(a,b)` 이후의 증명이 y가 무엇인지 알 수 있습니다.
        //          Unit 타입(등식이 무의미)과 함수 타입(함수 동치 미지원)은 생략.
        //       3. 본문은 같은 expected 타입에 대해 계속 검사합니다 — 바인딩된 사실은
        //          환경에 남고, 반환할 타입은 필요 없습니다.
        // [ENG] The parser converts blocks into Let chains, so every block statement
        //       passes through this rule. Its job is to deposit what each statement
        //       teaches us into the environment, so verification conditions generated
        //       later in the same scope can use it:
        //       1. Wildcard upgrade — even if a value is bound to `_`, when its type
        //          carries a condition (e.g. a lemma call's result type carries its
        //          postcondition) we invent an internal name and bind it. Only named
        //          bindings are picked up by to_logical_context, so the name is what
        //          lets the condition reach the logical context.
        //       2. Defining equation — add `name == right-hand side` as a path
        //          condition. The language has no side effects, so this equation is
        //          always true. It is what lets proofs after `let y = add(a,b)` know
        //          what y is. Skipped for Unit-typed values (the equation would be
        //          meaningless) and function-typed values (no function equality).
        //       3. Keep checking the body against the same expected type — the bound
        //          facts stay in the environment; no type needs to be returned.
        Expr::Let { pat, bound_expr, body } => {
            let bound_type = synthesize_expr(env, bound_expr, global_specs, vcs);
            env.with_scope(|inner_env| {
                // [1] Bind, upgrading interesting wildcards to fresh names.
                let bound_name: Option<Ident> = match pat {
                    Pattern::Ident(name) => {
                        bind_pattern_vars(inner_env, pat, &bound_type);
                        Some(name.clone())
                    }
                    Pattern::Wildcard => match base_of(&bound_type) {
                        // Unit-typed bounds with no refinement carry no knowledge
                        // (e.g. Instantiate links) — keep the historical no-op.
                        Some(BaseType::Unit) if !matches!(bound_type, Type::Refined(_)) => None,
                        // Arrow-typed bounds: functions are never named into Γ.
                        None => None,
                        _ => {
                            let fresh = inner_env.fresh("_bind");
                            inner_env.insert_var(fresh.clone(), bound_type.clone());
                            Some(fresh)
                        }
                    },
                    // Constructor/Tuple patterns: bind the field variables at
                    // their declared field types; the defining equation is
                    // added below using the pattern written as a term.
                    _ => {
                        bind_pattern_vars(inner_env, pat, &bound_type);
                        None
                    }
                };

                // [2] Defining equation: name == right-hand side
                //     (or pattern == right-hand side for destructuring patterns).
                let selfify = match base_of(&bound_type) {
                    Some(BaseType::Unit) | None => false, // Unit or Arrow: no equation
                    Some(_) => true,
                };
                if selfify {
                    if let Some(name) = &bound_name {
                        inner_env.add_path_condition(Expr::BinOp {
                            op: BinOp::Eq,
                            left: Box::new(Expr::Var(name.clone())),
                            right: Box::new((**bound_expr).clone()),
                        });
                    } else if !matches!(pat, Pattern::Wildcard) {
                        // Constructor/Tuple pattern: bound_expr == pattern-as-term.
                        inner_env.add_path_condition(build_pattern_eq_expr(bound_expr, pat));
                    }
                }

                // [3] Continue in checking mode.
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
        
        // ---------------------------------------------------------
        // [T-IF]: if-then-else (Checking Mode)
        // ---------------------------------------------------------
        // An `if` in a proof body splits the proof in two, the same way a
        // match splits it by constructor shape. Each branch is checked
        // against the same expected type inside its own scope, with the
        // guard recorded as a path condition: the then-branch may assume
        // the condition holds, the else-branch may assume its negation.
        // Checking the branches (instead of synthesizing them, as the
        // fallback below would) is what allows a `match` to appear inside
        // an `if` branch -- match is only implemented in checking mode --
        // so a proof can split on a guard first and on a constructor
        // shape second, mirroring function bodies that interleave the two.
        Expr::If { cond, then_expr, else_expr } => {
            // The condition must be Bool. Synthesizing it also lets any
            // calls inside it contribute their own verification conditions.
            let cond_type = synthesize_expr(env, cond, global_specs, vcs);
            let base_cond = match cond_type {
                Type::Base(b) | Type::Refined(RefinedType { base: b, .. }) => b,
                _ => panic!("Condition must be a base type (Bool)"),
            };
            if base_cond != BaseType::Bool {
                panic!("Condition of if-expression must be Bool");
            }

            env.with_scope(|inner_env| {
                inner_env.add_path_condition((**cond).clone());
                check_expr(inner_env, then_expr, expected, global_specs, vcs);
            });

            env.with_scope(|inner_env| {
                inner_env.add_path_condition(Expr::UnOp {
                    op: UnOp::Not,
                    expr: cond.clone(),
                });
                check_expr(inner_env, else_expr, expected, global_specs, vcs);
            });
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

            // [KOR] 기대 조건이 문자 그대로 `true`이면(정제 없는 매개변수에 인자를 넘길 때 등)
            //       VC `Γ ∧ e_1 ⇒ true`는 문맥과 무관하게 참이므로 goal을 만들지 않습니다.
            // [ENG] An expected predicate that is literally `true` (e.g. an argument passed
            //       to an unrefined parameter) makes the VC `Γ ∧ e_1 ⇒ true`, valid whatever
            //       the context says: no goal is generated.
            if matches!(pred_exp, Expr::BoolConst(true)) {
                return;
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
                let vc = inner_env.build_implication(pred_exp.clone());
                
                // -----------------------------------------------------------------
                // CONSEQUENCE: \Gamma \vdash \{\nu:B \mid e_1\} <: \{\nu:B \mid e_2\}
                // -----------------------------------------------------------------
                // [ENG] Collect manually provided instantiations for this specific scope.
                let mut all_insts = inner_env.get_active_instantiations();

                // [ENG] Automatic CEGQI Instantiation:
                //       Scan the entire logical context and the expected target expression.
                //       Extract all safe ground terms (functions/constructors) to automatically 
                //       inject them as instantiation hints, relieving the user from writing manual hints.
                let context_expr = inner_env.to_logical_context();
                let mut auto_insts = crate::auto_inst::collect_ground_terms(&context_expr);
                auto_insts.append(&mut crate::auto_inst::collect_ground_terms(&pred_exp));

                // [ENG] Merge auto-collected hints with manual hints, ensuring no duplicates.
                for inst in auto_insts {
                    if !all_insts.contains(&inst) {
                        all_insts.push(inst);
                    }
                }

                // [ENG] Package the VC and its tailored instantiations into a SubGoal.
                vcs.push(SubGoal {
                    property: vc,
                    instantiations: all_insts,
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
        (Pattern::Constructor { name, args, arg_types }, _) => {
            // [KOR] 필드 sort는 resolve_pattern_types가 새겨둔 arg_types에서 읽습니다.
            // [ENG] Field sorts come from arg_types, stamped by resolve_pattern_types.
            let field_types = arg_types.as_ref().unwrap_or_else(|| panic!(
                "Constructor pattern '{}' has unresolved field types (resolve_pattern_types was not run)",
                name
            ));
            for (arg_pat, field_ty) in args.iter().zip(field_types.iter()) {
                bind_pattern_vars(env, arg_pat, &Type::Base(field_ty.clone()));
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
        Pattern::Constructor { name, args, .. } => {
            Expr::Constructor { name: name.clone(), args: args.iter().map(pattern_to_expr).collect() }
        }
        Pattern::Tuple(elems) => Expr::Tuple(elems.iter().map(pattern_to_expr).collect()),
    }
}

/// Renames every parameter of a function signature to a fresh name, rewriting
/// all references to it in the rest of the signature (later parameter types and
/// the return refinement). After this, substituting actual arguments for the
/// parameters can never collide with a name the caller happens to use, because
/// no caller variable can share a name with a freshly generated parameter.
fn freshen_params(env: &mut TypeEnv, ty: Type) -> Type {
    match ty {
        Type::Arrow(f) => {
            let fresh = env.fresh("_arg");
            // References to this parameter live in the remainder of the
            // signature; its own refinement refers to it via its bound
            // variable, which is untouched by design.
            let renamed_ret =
                substitute_expr_in_type(&f.ret_type, &f.param_name, &Expr::Var(fresh.clone()));
            Type::Arrow(FunType {
                param_name: fresh,
                param_type: f.param_type,
                ret_type: Box::new(freshen_params(env, renamed_ret)),
            })
        }
        other => other,
    }
}

/// [KOR] 타입의 밑바탕 BaseType을 돌려줍니다 (함수 타입이면 None). Let 규칙이
///       "Unit이면 등식 생략 / 함수 타입이면 이름 부여 생략"을 판단할 때 사용합니다.
/// [ENG] Returns the underlying BaseType (None for a function type). Used by the
///       Let rule to decide "skip the equation for Unit / skip naming for
///       function-typed values".
fn base_of(ty: &Type) -> Option<BaseType> {
    match ty {
        Type::Base(b) => Some(b.clone()),
        Type::Refined(r) => Some(r.base.clone()),
        Type::Arrow(_) => None,
    }
}

/// Panics unless `ty` has the base sort `expected` (used by T-LOGIC).
fn expect_base(ty: &Type, expected: &BaseType, what: &str) {
    if base_of(ty).as_ref() != Some(expected) {
        panic!("T-LOGIC: {} must be {:?}, got {:?}", what, expected, base_of(ty));
    }
}

/// `{v: Bool | v == e}`: the selfified type of a Bool-valued program expression.
fn selfified_bool(e: Expr) -> Type {
    Type::Refined(RefinedType {
        bound_var: "v".to_string(),
        base: BaseType::Bool,
        predicate: Expr::BinOp {
            op: BinOp::Eq,
            left: Box::new(Expr::Var("v".to_string())),
            right: Box::new(e),
        },
    })
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
