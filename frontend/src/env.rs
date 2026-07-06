//! deptypes/src/env.rs
//! F* 스타일의 Dependent Type Checking을 위한 타입 환경(Type Environment, Γ)

use std::collections::HashMap;
use crate::ast::{Ident, Type, Expr, BinOp};

/// 하나의 스코프(블록) 내에서 선언된 변수들과 경로 조건들을 담습니다.
#[derive(Debug, Clone)]
pub struct Scope {
    /// 변수명 -> 타입 맵핑
    pub bindings: HashMap<Ident, Type>,
    /// 현재 스코프에서 참(True)이라고 가정할 수 있는 논리식들 (예: if x > 0 안에서의 x > 0)
    pub path_conditions: Vec<Expr>,
    /// [ENG] Instantiations manually provided within this specific scope.
    pub instantiations: Vec<Expr>,
}

impl Default for Scope {
    fn default() -> Self {
        Self {
            bindings: HashMap::new(),
            path_conditions: Vec::new(),
            instantiations: Vec::new(),
        }
    }
}

/// 전체 타입 환경 (Gamma)
/// 스코프의 스택으로 구성되어 섀도잉(Shadowing)과 지역 변수를 관리합니다.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    scopes: Vec<Scope>,
}

impl TypeEnv {
    /// 빈 타입 환경을 생성합니다. 기본적으로 전역 스코프 1개를 가집니다.
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::default()],
        }
    }

    /// [ENG] Injects a manual instantiation hint into the current (most deeply nested) scope.
    pub fn add_instantiation(&mut self, expr: Expr) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.instantiations.push(expr);
        }
    }

    /// [ENG] Collects all instantiations active in the current environment across all scopes.
    pub fn get_active_instantiations(&self) -> Vec<Expr> {
        let mut active_insts = Vec::new();
        for scope in &self.scopes {
            for inst in &scope.instantiations {
                active_insts.push(inst.clone());
            }
        }
        active_insts
    }

    pub fn close_formula(&self, target: Expr) -> Expr {
        let mut binders = Vec::new();
        // 모든 스코프를 뒤져서 변수와 그 뼈대 타입(BaseType)을 수집
        for scope in &self.scopes {
            for (var_name, ty) in &scope.bindings {
                let base_ty = match ty {
                    Type::Base(b) => b.clone(),
                    Type::Refined(r) => r.base.clone(),
                    Type::Arrow(_) => continue, // 함수는 양화 대상에서 제외
                };
                binders.push((var_name.clone(), base_ty));
            }
        }
        
        // 수집된 변수가 있다면 Forall로 감싸서 반환
        if binders.is_empty() {
            target
        } else {
            Expr::Forall {
                binders,
                body: Box::new(target),
            }
        }
    }

    /// 🌟 [핵심] 새로운 스코프를 열고 주어진 클로저(작업)를 수행한 뒤, 스코프를 닫습니다.
    ///
    /// # `with_scope`의 역할과 원리 🌟
    /// 
    /// 프로그래밍 언어에서 `if` 블록이나 `match` 블록 안에서 선언된 변수나 조건은
    /// 그 블록을 빠져나가는 순간 사라져야 합니다(스코프 소멸). 
    /// 의존 타입 체킹(Dependent Type Checking) 과정에서도 마찬가지입니다.
    /// 특정 블록(예: `if x > 0`)을 검사할 때만 `x > 0`이라는 사실이 유효하며,
    /// 블록 밖에서는 이 사실을 증명(VC 생성)에 사용하면 안 됩니다.
    ///
    /// `with_scope`는 이 **"임시적인 논리적 문맥(Local Context)"**을 완벽하게 관리해주는 핵심 함수입니다.
    ///
    /// ## 예시 1: 제어 흐름 (if-then-else)
    /// ```fstar
    /// let z = if x > 0 {
    ///     x + 1 // 이 블록 안에서는 무조건 x > 0 임을 가정할 수 있음
    /// } else {
    ///     0     // 이 블록 안에서는 무조건 !(x > 0) 임을 가정할 수 있음
    /// }
    /// // 이 지점에서는 x > 0인지 아닌지 전혀 알 수 없음!
    /// ```
    /// * **작동 방식**:
    ///   1. `with_scope` 호출: `scopes` 스택에 빈 `Scope` 하나를 푸시(push)합니다.
    ///   2. 클로저 실행: 안에서 `env.add_path_condition(x > 0)`을 호출해 임시 스코프에 조건을 넣습니다.
    ///   3. `x + 1`을 검사(typecheck)합니다. 이때 `x > 0`이 적용되어 안전하게 증명됩니다.
    ///   4. **스코프 닫기**: 클로저가 끝나면 `scopes.pop()`이 실행되어, 방금 넣었던 `x > 0` 조건이 깔끔하게 증발합니다!
    ///
    /// ## 예시 2: 함수 서브타이핑 (DEC-<:FUN) 에서의 인자 가정
    /// ```fstar
    /// // 요구되는 함수 타입 (f2): y:Int -> {r:Int | r > y}
    /// // 내가 가진 함수 타입 (f1): x:Int -> {r:Int | r > x}
    /// ```
    /// * **작동 방식**:
    ///   우리가 $f_1$이 $f_2$를 대체할 수 있는지(반환값이 조건을 만족하는지) 검사하려면,
    ///   먼저 **호출자가 $f_2$의 규칙에 맞게 올바른 인자 `y`를 넘겨주었다고 "가정(Assume)"** 해야 합니다.
    ///   1. `with_scope` 호출: 임시 스코프 생성.
    ///   2. 클로저 실행: $f_2$의 파라미터 타입(`S1`)을 $f_1$의 파라미터 이름(`x`)으로 묶어서 환경에 추가합니다. `inner_env.insert_var(x, S1)`
    ///      (즉, "지금부터 반환값을 검사할 동안은 인자 `x`가 `S1` 조건을 만족한다고 믿어보자!" 라는 뜻입니다.)
    ///   3. 반환값 타입 서브타이핑 검사: 이 가정 하에 `T2 <: S2[x/y]` 를 검사합니다.
    ///   4. **스코프 닫기**: 검사가 끝나면 `scopes.pop()`으로 가정을 파기합니다. (다른 함수 검사에 영향을 주지 않음)
    ///
    pub fn with_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.scopes.push(Scope::default());
        let result = f(self);
        self.scopes.pop();
        result
    }

    /// 현재 스코프에 변수와 타입을 등록합니다.
    pub fn insert_var(&mut self, name: Ident, ty: Type) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.bindings.insert(name, ty);
        }
    }

    /// 환경에서 변수의 타입을 찾습니다. (가장 최근 스코프부터 역순으로 검색)
    pub fn lookup_var(&self, name: &Ident) -> Option<&Type> {
        for scope in self.scopes.iter().rev() {
            if let Some(ty) = scope.bindings.get(name) {
                return Some(ty);
            }
        }
        None
    }

    /// 현재 스코프에 새로운 경로 조건(Path Condition)을 추가합니다.
    /// 예: if cond { ... } 를 검사할 때 cond 수식을 추가합니다.
    pub fn add_path_condition(&mut self, cond: Expr) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.path_conditions.push(cond);
        }
    }

    /// 🌟 [TODO 1] 환경의 모든 지식을 하나의 논리식(Expr)으로 뭉쳐서 반환합니다.
    /// 이 메서드가 반환하는 Expr은 SMT 솔버가 증명할 때 사용할 "모든 가정들의 교집합(AND)"입니다.
    pub fn to_logical_context(&self) -> Expr {
        let mut all_conditions: Vec<Expr> = Vec::new();

        for scope in &self.scopes {
            // 1. 변수들의 Refinement Type 조건 추출
            for (var_name, ty) in &scope.bindings {
                if let Type::Refined(ref_ty) = ty {
                    // TODO: ref_ty.predicate 안에는 bound_var (예: 'v')가 들어있습니다.
                    // 이것을 실제 변수명 var_name (예: 'x')으로 치환해야 합니다.
                    // 예: {v: Int | v > 0} -> 실제 논리식: x > 0
                    
                    let substituted_expr = substitute_expr(
                        &ref_ty.predicate, 
                        &ref_ty.bound_var, 
                        &Expr::Var(var_name.clone())
                    );
                    all_conditions.push(substituted_expr);
                }
            }

            // 2. 제어 흐름 상의 Path Condition 추가
            for cond in &scope.path_conditions {
                all_conditions.push(cond.clone());
            }
        }

        // 3. 수집된 모든 조건을 AND(&&) 연산자로 묶어서 하나의 Expr로 반환합니다.
        build_and_tree(all_conditions)
    }

    /// 🌟 목표 논리식(Target)을 증명하기 위한 최종 VC(Verification Condition)를 생성합니다.
    /// 반환되는 수식의 형태: [[Gamma]] => Target
    pub fn build_implication(&self, target: Expr) -> Expr {
        let context_expr = self.to_logical_context();
        let implication = Expr::BinOp {
            op: BinOp::Implies,
            left: Box::new(context_expr),
            right: Box::new(target),
        };

        self.close_formula(implication)
    }
}

// ============================================================================
// 🛠️ 아래 함수들은 구현이 필요한 헬퍼 함수들입니다. (ast.rs에 두어도 좋습니다)
// ============================================================================

/// [TODO 2] 수식(expr) 내부의 특정 변수(target_var)를 다른 수식(replacement)으로 치환합니다.
/// 이 함수는 재귀적으로 AST를 순회하며 만들어야 합니다.
pub fn substitute_expr(expr: &Expr, target_var: &Ident, replacement: &Expr) -> Expr {
    match expr {
        // 1. 단순 치환
        Expr::BoolConst(_) => expr.clone(),
        Expr::Var(name) => {
            if name == target_var {
                replacement.clone()
            } else {
                expr.clone()
            }
        },

        // 2. 재귀적 순회
        Expr::Tuple(exprs) => {
            let new_exprs = exprs.iter()
                .map(|e| substitute_expr(e, target_var, replacement))
                .collect();
            Expr::Tuple(new_exprs)
        },
        Expr::BinOp { op, left, right } => Expr::BinOp {
            op: op.clone(),
            left: Box::new(substitute_expr(left, target_var, replacement)),
            right: Box::new(substitute_expr(right, target_var, replacement)),
        },
        Expr::UnOp { op, expr: inner } => Expr::UnOp {
            op: op.clone(),
            expr: Box::new(substitute_expr(inner, target_var, replacement)),
        },
        Expr::If { cond, then_expr, else_expr } => Expr::If {
            cond: Box::new(substitute_expr(cond, target_var, replacement)),
            then_expr: Box::new(substitute_expr(then_expr, target_var, replacement)),
            else_expr: Box::new(substitute_expr(else_expr, target_var, replacement)),
        },
        Expr::Call { func, args } => {
            let new_args = args.iter()
                .map(|arg| substitute_expr(arg, target_var, replacement))
                .collect();
            Expr::Call {
                func: func.clone(), // 함수 이름은 치환 대상이 아님
                args: new_args,
            }
        },
        Expr::Constructor { name, args } => {
            let new_args = args.iter()
                .map(|arg| substitute_expr(arg, target_var, replacement))
                .collect();
            Expr::Constructor {
                name: name.clone(),
                args: new_args,
            }
        },
        Expr::ApplyRel { relation, args } => {
            let new_args = args.iter()
                .map(|arg| substitute_expr(arg, target_var, replacement))
                .collect();
            Expr::ApplyRel {
                relation: relation.clone(),
                args: new_args,
            }
        },

        // 3. 🚨 변수 섀도잉(Shadowing) 방어
        Expr::Let { pat, bound_expr, body } => {
            // bound_expr는 바깥쪽 스코프이므로 무조건 치환
            let new_bound = Box::new(substitute_expr(bound_expr, target_var, replacement));
            
            // 만약 패턴(pat)에서 target_var와 같은 이름의 변수를 새로 선언했다면?
            // body 내부의 target_var는 섀도잉되므로 치환을 멈춤(그대로 둠).
            let new_body = if pattern_contains_var(pat, target_var) {
                body.clone()
            } else {
                Box::new(substitute_expr(body, target_var, replacement))
            };

            Expr::Let {
                pat: pat.clone(),
                bound_expr: new_bound,
                body: new_body,
            }
        },
        Expr::Match { expr: match_expr, arms } => {
            let new_match_expr = Box::new(substitute_expr(match_expr, target_var, replacement));
            
            let new_arms = arms.iter().map(|(pat, arm_expr)| {
                // 패턴이 target_var를 가린다면 arm_expr 치환을 멈춤
                let new_arm_expr = if pattern_contains_var(pat, target_var) {
                    arm_expr.clone()
                } else {
                    substitute_expr(arm_expr, target_var, replacement)
                };
                (pat.clone(), new_arm_expr)
            }).collect();

            Expr::Match {
                expr: new_match_expr,
                arms: new_arms,
            }
        },

        Expr::Forall { binders, body } => {
            // 만약 새로 바인딩되는 변수들 중에 치환 대상(target_var)과 같은 이름이 있다면,
            // 그 안쪽은 완전히 새로운 변수의 영역(Shadowing)이므로 치환을 멈춥니다!
            let is_shadowed = binders.iter().any(|(name, _)| name == target_var);
            let new_body = if is_shadowed {
                body.clone()
            } else {
                Box::new(substitute_expr(body, target_var, replacement))
            };

            Expr::Forall {
                binders: binders.clone(),
                body: new_body,
            }
        },
        Expr::Exists { binders, body } => {
            let is_shadowed = binders.iter().any(|(name, _)| name == target_var);
            let new_body = if is_shadowed {
                body.clone()
            } else {
                Box::new(substitute_expr(body, target_var, replacement))
            };

            Expr::Exists {
                binders: binders.clone(),
                body: new_body,
            }
        },
        Expr::Instantiate(inner) => {
            Expr::Instantiate(Box::new(substitute_expr(inner, target_var, replacement)))
        },
        Expr::ExistentialBindings(bindings) => {
            let new_bindings = bindings.iter().map(|(id, e)| {
                (id.clone(), substitute_expr(e, target_var, replacement))
            }).collect();
            Expr::ExistentialBindings(new_bindings)
        },
    }
}

// 헬퍼: 패턴 안에 특정 변수명이 존재하는지 검사 (섀도잉 확인용)
use crate::ast::Pattern;
fn pattern_contains_var(pat: &Pattern, var: &Ident) -> bool {
    match pat {
        Pattern::Wildcard => false,
        Pattern::Ident(name) => name == var,
        Pattern::Constructor { args, .. } | Pattern::Tuple(args) => {
            args.iter().any(|p| pattern_contains_var(p, var))
        }
    }
}

/// Vec<Expr>에 담긴 여러 조건식들을 BinOp::And 연산으로 묶어 하나의 트리로 만듭니다.
fn build_and_tree(conditions: Vec<Expr>) -> Expr {
    // 1. 조건이 하나도 없으면 "항상 참(True)"을 반환합니다.
    if conditions.is_empty() {
        return Expr::BoolConst(true);
    }
    
    // 2. 조건들을 하나씩 꺼내기 위해 iterator를 만듭니다.
    let mut iter = conditions.into_iter();
    
    // 3. 첫 번째 조건을 트리의 뿌리(root)로 삼습니다.
    let mut root = iter.next().unwrap();
    
    // 4. 나머지 조건들을 순회하면서 기존 root와 AND(&&)로 계속 묶어나갑니다.
    for cond in iter {
        root = Expr::BinOp {
            op: BinOp::And,
            left: Box::new(root),
            right: Box::new(cond),
        };
    }
    
    // 5. 완성된 거대한 AND 트리를 반환합니다.
    root
}