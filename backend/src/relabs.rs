//! backend/src/relabs.rs
//! 관계적 추상화 (Relational Abstraction) 변환기
//!
//! [KOR] ANF(A-Normal Form)와 NNF(Negation Normal Form) 변환을 마친 수식을 순회하며,
//! 모든 함수 호출 및 생성자 호출(Call, Constructor) 노드를 SMT 솔버가 이해할 수 있는
//! 순수 관계식(ApplyRel)과 양화사(Forall/Exists)로 변환합니다.
//! 이를 통해 비선형 정수 산술(LIA)을 배제하고 EPR(Extended Effectively Propositional)
//! 결정 가능 프래그먼트 내에 수식을 가둡니다.
//!
//! 💡 [TODO: Tuple Flattening (튜플 평탄화)]
//! 현재는 함수의 반환값이 단일 변수(x)라고 가정하고 양화사(Forall(x))와 관계식(f_rel(args, x))을 생성합니다.
//! 하지만 f가 튜플 (Int, Bool)을 반환한다면, SMT의 결정 가능성(Decidability)을 위해 
//! 이를 개별 변수 x_0, x_1로 쪼개어 `Forall(x_0, x_1). f_rel(args, x_0, x_1)` 형태로 
//! 평탄화(Flattening)하는 로직이 향후 추가되어야 합니다.
//!
//! [ENG] Traverses expressions processed by ANF and NNF, converting all function and 
//! constructor calls into pure relations (ApplyRel) and quantifiers (Forall/Exists) 
//! understandable by the SMT solver. This eliminates LIA and confines the logic 
//! within the decidable EPR fragment.
//!
//! 💡 [TODO: Tuple Flattening]
//! Currently, we assume functions return a single variable 'x' and generate Forall(x) 
//! with f_rel(args, x). If a function returns a tuple like (Int, Bool), we must flatten 
//! it into individual variables x_0, x_1 for SMT decidability, resulting in 
//! `Forall(x_0, x_1). f_rel(args, x_0, x_1)`. This logic should be implemented in the future.

use std::collections::HashMap;
use frontend::ast::{Expr, Ident, UnOp, BinOp, BaseType, Pattern, FunctionDef, Type};

/// [KOR] 수식을 관계적 추상화 형태로 변환하는 진입점입니다.
///       초기 극성(Polarity)은 참(true, 긍정)으로 시작합니다.
///       정확한 타입 추론을 위해 `global_specs`를 주입받습니다.
/// [ENG] Entry point for Relational Abstraction. Initial polarity is positive (true).
///       Receives `global_specs` to infer accurate return types.
pub fn transform_expr(expr: &Expr, global_specs: &HashMap<Ident, FunctionDef>) -> Expr {
    relabs(expr, true, global_specs)
}

/// [KOR] 핵심 관계적 추상화 함수.
///       `is_pos`는 현재 AST 노드의 극성(Polarity)을 나타냅니다.
///       NNF 변환이 선행되었으므로, `UnOp::Not`을 만날 때마다 `is_pos`를 뒤집으면 됩니다.
/// [ENG] Core Relational Abstraction function. `is_pos` indicates the polarity.
///       Since NNF has been applied, we just flip `is_pos` whenever we hit `UnOp::Not`.
fn relabs(expr: &Expr, is_pos: bool, global_specs: &HashMap<Ident, FunctionDef>) -> Expr {
    match expr {
        // --------------------------------------------------------------------
        // 1. Let 바인딩 (ANF 평탄화의 핵심 타겟)
        //    let x = f(args) in body  =>  ∀/∃ x. f_rel(args, x) =>/&& body
        // --------------------------------------------------------------------
        Expr::Let { pat, bound_expr, body } => {
            // ANF 단계에서 `pat`은 반드시 단순 변수(Ident)로 평탄화되어야 함
            let var_name = match pat {
                Pattern::Ident(name) => name.clone(),
                _ => panic!("RelAbs expects ANF-flattened Let with simple Ident pattern, got {:?}", pat),
            };

            // 바인딩된 수식(`bound_expr`)에 따라 관계식으로 쪼갤지 결정
            match &**bound_expr {
                // 일반 함수 호출 (f(args))
                Expr::Call { func, args } => {
                    transform_call_to_rel(
                        &var_name, 
                        func, 
                        args, 
                        body, 
                        is_pos,
                        global_specs
                    )
                }
                // 생성자 호출 (Constructor(args))
                Expr::Constructor { name, args } => {
                    if args.is_empty() {
                        // A constructor with no arguments denotes a constant (it is
                        // declared as one for the solver). Binding a variable to a
                        // constant introduces no relation, and the final translation
                        // stage accepts no Let nodes -- so replace the variable by
                        // the constant everywhere in the body and drop the binding.
                        let const_name = name.replace("::", "__");
                        let inlined = frontend::env::substitute_expr(
                            body,
                            &var_name,
                            &Expr::Var(const_name),
                        );
                        relabs(&inlined, is_pos, global_specs)
                    } else {
                        // 인자가 있는 생성자는 기존처럼 관계식으로 변환
                        transform_call_to_rel(
                            &var_name,
                            name,
                            args,
                            body,
                            is_pos,
                            global_specs
                        )
                    }
                }
                // 만약 바운드된 수식이 이미 ApplyRel이라면(드문 케이스지만), 그 자체를 사용
                Expr::ApplyRel { relation, args } => {
                    transform_call_to_rel(
                        &var_name,
                        relation,
                        args,
                        body,
                        is_pos,
                        global_specs
                    )
                }
                // A binding whose right-hand side is already an atomic value
                // carries no relational content, and the final translation stage
                // accepts no Let nodes -- inline the value into the body and drop
                // the binding. Such bindings arise when the flattening stage names
                // the result of an inner expression and a source-level `let` then
                // aliases that name (e.g. `let y = S(x); ...` flattens to
                // `let anf_0 = S(x) in let y = anf_0 in ...`).
                Expr::Var(alias) if alias.starts_with("anf_") => {
                    // Names produced by the flattening stage are globally unique,
                    // so this substitution can never capture anything.
                    let inlined =
                        frontend::env::substitute_expr(body, &var_name, &Expr::Var(alias.clone()));
                    relabs(&inlined, is_pos, global_specs)
                }
                Expr::BoolConst(_) => {
                    let inlined =
                        frontend::env::substitute_expr(body, &var_name, bound_expr);
                    relabs(&inlined, is_pos, global_specs)
                }
                // Anything else (e.g. tuples) is kept; the final translation stage
                // will report it loudly if it cannot be encoded.
                _ => {
                    Expr::Let {
                        pat: pat.clone(),
                        bound_expr: Box::new(relabs(bound_expr, is_pos, global_specs)),
                        body: Box::new(relabs(body, is_pos, global_specs)),
                    }
                }
            }
        }

        // --------------------------------------------------------------------
        // 2. 극성 제어 연산자들 (Polarity Control)
        // --------------------------------------------------------------------
        Expr::UnOp { op: UnOp::Not, expr: inner } => {
            Expr::UnOp {
                op: UnOp::Not,
                expr: Box::new(relabs(inner, !is_pos, global_specs)), // 극성 반전
            }
        }

        Expr::BinOp { op, left, right } => {
            match op {
                BinOp::Implies => {
                    // A => B 에서 A는 부정 극성, B는 긍정 극성을 가짐
                    Expr::BinOp {
                        op: BinOp::Implies,
                        left: Box::new(relabs(left, !is_pos, global_specs)),
                        right: Box::new(relabs(right, is_pos, global_specs)),
                    }
                }
                // And, Or, Eq, Neq 등은 하위 수식으로 극성을 그대로 전달
                _ => {
                    Expr::BinOp {
                        op: op.clone(),
                        left: Box::new(relabs(left, is_pos, global_specs)),
                        right: Box::new(relabs(right, is_pos, global_specs)),
                    }
                }
            }
        }

        // --------------------------------------------------------------------
        // 3. 양화사 (Quantifiers)
        // --------------------------------------------------------------------
        Expr::Forall { binders, body } => {
            Expr::Forall {
                binders: binders.clone(),
                body: Box::new(relabs(body, is_pos, global_specs)),
            }
        }
        Expr::Exists { binders, body } => {
            Expr::Exists {
                binders: binders.clone(),
                body: Box::new(relabs(body, is_pos, global_specs)),
            }
        }

        // --------------------------------------------------------------------
        // 4. 제어 흐름 (Control Flow)
        // --------------------------------------------------------------------
        Expr::If { cond, then_expr, else_expr } => {
            Expr::If {
                cond: Box::new(relabs(cond, is_pos, global_specs)),
                then_expr: Box::new(relabs(then_expr, is_pos, global_specs)),
                else_expr: Box::new(relabs(else_expr, is_pos, global_specs)),
            }
        }

        // --------------------------------------------------------------------
        // 5. 수동 인스턴스화 (ExistentialBindings)
        // --------------------------------------------------------------------
        Expr::ExistentialBindings(bindings) => {
            // [KOR] 사용자가 강제한 인스턴스화이므로, 극성(is_pos)에 상관없이 무조건 Exists와 And로 결합합니다.
            // [ENG] Since this is a manual instantiation forced by the user, we unconditionally bind them
            //       with Exists and And, ignoring the current polarity (is_pos).
            let mut current_expr = Expr::BoolConst(true);
            
            // 바인딩을 역순으로 순회하며 Exists와 And로 감쌉니다.
            for (var_name, bound_expr) in bindings.iter().rev() {
                match bound_expr {
                    Expr::Call { func, args } | Expr::Constructor { name: func, args } => {
                        if args.is_empty() && matches!(bound_expr, Expr::Constructor { .. }) {
                            // 인자가 없는 생성자는 관계식이 아니므로 무시합니다.
                            continue;
                        }
                        
                        let ret_base_type = get_return_base_type(func, global_specs);
                        let binders = vec![(var_name.clone(), ret_base_type)];
                        
                        let mut rel_args = Vec::new();
                        for arg in args {
                            rel_args.push(relabs(arg, is_pos, global_specs));
                        }
                        rel_args.push(Expr::Var(var_name.clone()));
                        
                        let apply_rel = Expr::ApplyRel {
                            relation: format!("{}_rel", func),
                            args: rel_args,
                        };
                        
                        current_expr = Expr::Exists {
                            binders,
                            body: Box::new(Expr::BinOp {
                                op: BinOp::And,
                                left: Box::new(apply_rel),
                                right: Box::new(current_expr),
                            }),
                        };
                    }
                    Expr::ApplyRel { relation, args } => {
                        let ret_base_type = get_return_base_type(relation, global_specs);
                        let binders = vec![(var_name.clone(), ret_base_type)];
                        
                        let mut rel_args = Vec::new();
                        for arg in args {
                            rel_args.push(relabs(arg, is_pos, global_specs));
                        }
                        rel_args.push(Expr::Var(var_name.clone()));
                        
                        let apply_rel = Expr::ApplyRel {
                            relation: relation.clone(),
                            args: rel_args,
                        };
                        
                        current_expr = Expr::Exists {
                            binders,
                            body: Box::new(Expr::BinOp {
                                op: BinOp::And,
                                left: Box::new(apply_rel),
                                right: Box::new(current_expr),
                            }),
                        };
                    }
                    _ => unreachable!("Only Call, Constructor, and ApplyRel can be existential bindings"),
                }
            }
            current_expr
        }

        // --------------------------------------------------------------------
        // 6. 리프 노드 (Leaf Nodes) - 수정 없이 통과
        // --------------------------------------------------------------------
        Expr::BoolConst(_) | Expr::Var(_) | Expr::Tuple(_) | Expr::ApplyRel { .. } | Expr::Instantiate(_) => {
            expr.clone()
        }

        // --------------------------------------------------------------------
        // 7. 에러 케이스 (Error Cases)
        // --------------------------------------------------------------------
        Expr::Constructor { name, args } if args.is_empty() => {
            // 인자가 없는 생성자는 상수로 취급되어 ANF에서 Let으로 감싸지 않고 맨몸으로 넘어옵니다.
            let const_name = name.replace("::", "__");
            Expr::Var(const_name)
        }
        Expr::Call { .. } | Expr::Constructor { .. } => {
            panic!("RelAbs Error: Found bare Call/Constructor. ANF should have wrapped these in Let bindings.");
        }
        Expr::Match { .. } => {
            panic!("RelAbs Error: Match should have been eliminated during Eval phase.");
        }
    }
}

// ============================================================================
// 🛠️ Helper Functions
// ============================================================================

/// [KOR] 전역 시그니처 환경을 조회하여 함수나 생성자의 최종 반환 BaseType을 알아냅니다.
/// [ENG] Looks up the global signature environment to determine the final return BaseType of a function or constructor.
fn get_return_base_type(func_name: &str, global_specs: &HashMap<Ident, FunctionDef>) -> BaseType {
    if let Some(def) = global_specs.get(func_name) {
        // [KOR] 종속 함수 타입(Arrow)의 끝까지 찾아내려가서 최종 반환 타입을 얻음
        let mut current = &def.signature;
        while let Type::Arrow(fun_type) = current {
            current = &*fun_type.ret_type;
        }
        match current {
            Type::Base(b) => b.clone(),
            Type::Refined(r) => r.base.clone(),
            Type::Arrow(_) => unreachable!("Arrow type should have been fully unwrapped"),
        }
    } else if let Some(idx) = func_name.find("::") {
        // [KOR] 생성자의 경우 "타입::생성자명" 형식이므로 앞부분을 추출함. (예: Nat::Z => Nat)
        // [ENG] For constructors, extract the prefix before "::" as the custom sort name.
        BaseType::Custom(func_name[..idx].to_string())
    } else {
        // [KOR] 알 수 없는 경우 (주로 SMT 내장 함수 등), 임시로 Custom Sort 사용
        // [ENG] Fallback for unknown functions (e.g., built-in SMT functions)
        BaseType::Custom(func_name.to_string())
    }
}

/// Does `expr` mention the variable `name` anywhere?
fn mentions_var(expr: &Expr, name: &Ident) -> bool {
    match expr {
        Expr::Var(v) => v == name,
        Expr::BoolConst(_) => false,
        Expr::Call { args, .. } | Expr::Constructor { args, .. } | Expr::ApplyRel { args, .. } | Expr::Tuple(args) => {
            args.iter().any(|a| mentions_var(a, name))
        }
        Expr::BinOp { left, right, .. } => mentions_var(left, name) || mentions_var(right, name),
        Expr::UnOp { expr, .. } | Expr::Instantiate(expr) => mentions_var(expr, name),
        Expr::If { cond, then_expr, else_expr } => {
            mentions_var(cond, name) || mentions_var(then_expr, name) || mentions_var(else_expr, name)
        }
        Expr::Let { bound_expr, body, .. } => mentions_var(bound_expr, name) || mentions_var(body, name),
        Expr::Match { expr, arms } => {
            mentions_var(expr, name) || arms.iter().any(|(_, e)| mentions_var(e, name))
        }
        Expr::Forall { body, .. } | Expr::Exists { body, .. } => mentions_var(body, name),
        Expr::ExistentialBindings(bs) => bs.iter().any(|(_, e)| mentions_var(e, name)),
    }
}

/// If `body` is the equality `var == t` or `t == var` with `var` not free in `t`,
/// return `t`: the call's result is pinned to a term the formula already names.
fn pinned_to<'a>(var: &Ident, body: &'a Expr) -> Option<&'a Expr> {
    if let Expr::BinOp { op: BinOp::Eq, left, right } = body {
        let is_var = |e: &Expr| matches!(e, Expr::Var(v) if v == var);
        if is_var(left) && !mentions_var(right, var) {
            return Some(right);
        }
        if is_var(right) && !mentions_var(left, var) {
            return Some(left);
        }
    }
    None
}

/// [KOR] `let var_name = func(args) in body` 형태를 관계적 추상화로 변환합니다.
///       - 긍정 극성일 경우: `Forall(var_name: RetType). func_rel(args..., var_name) => body`
///       - 부정 극성일 경우: `Exists(var_name: RetType). func_rel(args..., var_name) && body`
///
/// Peephole (after CamlStar `36bd5b7`): when `body` is exactly `var_name == t` with
/// `var_name` not free in `t`, emit the bare literal `func_rel(args..., t)` instead.
///   - negative polarity: `∃x. R(a,x) ∧ x = t  ≡  R(a,t)` (one-point rule), exact;
///   - positive polarity: `R(a,t)` is STRONGER than `∀x. R(a,x) ⇒ x = t` — given
///     functionality it equals that clause plus `∃x. R(a,x)`, a pointwise totality
///     instance whose witness the formula names. Sound because every relation is the
///     graph of a total function in every intended model, and still EPR because no
///     existential is written. Effect: a definitional leaf `f(args) = t` asserts that
///     `f(args)` EXISTS wherever the other terms of the leaf exist, so the result of a
///     pinned unfolding never needs an `instantiate!` hint (`doc/relabs_peephole.md`).
fn transform_call_to_rel(
    var_name: &Ident,
    func_name: &str,
    args: &[Expr],
    body: &Expr,
    is_pos: bool,
    global_specs: &HashMap<Ident, FunctionDef>,
) -> Expr {
    // 1. 관계식 적용 노드 생성: 인자 목록의 맨 마지막에 반환값을 받을 변수를 추가
    // let mut rel_args = args.to_vec();
    let mut rel_args = Vec::new();
    for arg in args {
        // 인자들에 대해서도 재귀적으로 relabs를 적용하여
        // 텅 빈 Constructor(예: Nat::Z)가 상수 Var(Nat__Z)로 잘 변환되게 합니다.
        rel_args.push(relabs(arg, is_pos, global_specs));
    }
    // [KOR] 원래의 함수명과 SMT 상의 관계식(Predicate)을 명확히 구분하기 위해 `_rel` 접미사를 붙입니다.
    //       (예: `union` => `union_rel`) 이를 통해 SMT 내장 함수나 다른 식별자와의 이름 충돌을 방지합니다.
    // [ENG] Append the `_rel` suffix to distinguish the relational predicate from the original function
    //       in SMT (e.g., `union` => `union_rel`). This prevents naming collisions with SMT built-ins or other identifiers.
    let relation = format!("{}_rel", func_name);

    // 2. 내부 Body 재귀 변환
    let inner_body = relabs(body, is_pos, global_specs);

    // Peephole: the result is pinned to a term the formula names -> bare literal.
    if let Some(t) = pinned_to(var_name, &inner_body) {
        rel_args.push(t.clone());
        return Expr::ApplyRel { relation, args: rel_args };
    }

    rel_args.push(Expr::Var(var_name.clone()));
    let apply_rel = Expr::ApplyRel { relation, args: rel_args };

    // 3. 변수 바인더 생성 (정확한 반환 타입 조회)
    // [KOR] 이전의 더미 타입("Unknown") 대신 `global_specs`를 조회하여 정확한 SMT Sort를 알아냅니다.
    // [ENG] Look up `global_specs` to infer the accurate SMT Sort instead of the dummy "Unknown" type.
    let ret_base_type = get_return_base_type(func_name, global_specs);
    let binders = vec![(var_name.clone(), ret_base_type)];

    // 4. 극성에 따른 논리 구조 결합
    if is_pos {
        // [KOR] 긍정 (Forall & Implies)
        Expr::Forall {
            binders,
            body: Box::new(Expr::BinOp {
                op: BinOp::Implies,
                left: Box::new(apply_rel),
                right: Box::new(inner_body),
            }),
        }
    } else {
        // [KOR] 부정 (Exists & And)
        Expr::Exists {
            binders,
            body: Box::new(Expr::BinOp {
                op: BinOp::And,
                left: Box::new(apply_rel),
                right: Box::new(inner_body),
            }),
        }
    }
}