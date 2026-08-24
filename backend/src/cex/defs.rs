//! [KOR] 함수 본문의 브랜치 분해와 정의 주석 블록.
//!
//! `decompose_body`는 함수 본문의 중첩된 match를 평탄화하여, 브랜치마다
//! "어느 파라미터가 어느 패턴을 취했는가"(bindings)와 그 브랜치의 잎
//! 표현식(rhs)을 돌려줍니다. If는 잎에 그대로 남습니다: 정의 표시는
//! `if g then a else b`를 한 줄로 렌더링하고, 가드를 방정식으로 쪼개는
//! 일은 이 분해를 소비하는 쪽의 몫입니다.
//!
//! `print_definitions`는 그 분해를 사람이 읽는 등식 주석으로 렌더링합니다:
//!
//! ```text
//! ; definitions:
//! ;   add(Z, y)          = y
//! ;   add(S(x_prime), y) = S(add(x_prime, y))
//! ```
//!
//! [ENG] Branch decomposition of function bodies, and the definitions
//! comment block.
//!
//! `decompose_body` flattens the nested matches of a function body,
//! returning per branch "which parameter took which pattern" (bindings)
//! and the branch's leaf expression (rhs). `If` stays in the leaf: the
//! definitions display renders `if g then a else b` on one line, and
//! splitting guards into separate equations is the consumer's job.
//!
//! `print_definitions` renders that decomposition as human-readable
//! equation comments (see the example above). Unlike the asserts in the
//! counterexample file (SMT-LIB s-expressions), these comments use math
//! style -- `f(a, b)` with commas -- because they are prose for the
//! reader, not solver input.

use std::collections::BTreeSet;

use frontend::ast::{BaseType, Expr, Ident, Pattern, Program, Type};

use super::print::{sorted_ci, variant_name};
use crate::smt::get_fun_types;

/// [KOR] 평탄화된 match 브랜치 하나.
/// [ENG] One flattened match branch.
pub struct Branch {
    /// [KOR] 바깥 match부터 안쪽 순서로, (매칭된 파라미터, 취한 패턴).
    /// [ENG] (matched parameter, pattern taken), outermost match first.
    pub bindings: Vec<(Ident, Pattern)>,
    /// [KOR] 브랜치의 잎 표현식. If를 포함할 수 있습니다.
    /// [ENG] The branch's leaf expression. May contain If.
    pub rhs: Expr,
}

/// [KOR] 함수 본문의 중첩 match를 브랜치 목록으로 평탄화합니다.
///       match 대상은 단순 변수여야 합니다 (백엔드 공리 생성과 같은 불변식).
/// [ENG] Flattens the nested matches of a function body into a list of
///       branches. Match targets must be simple variables (the same
///       invariant as backend axiom generation).
pub fn decompose_body(body: &Expr) -> Vec<Branch> {
    let mut branches = Vec::new();
    walk(body, &mut Vec::new(), &mut branches);
    branches
}

fn walk(expr: &Expr, bindings: &mut Vec<(Ident, Pattern)>, out: &mut Vec<Branch>) {
    if let Expr::Match { expr: target, arms } = expr {
        let matched_var = match &**target {
            Expr::Var(v) => v.clone(),
            other => panic!(
                "counterexample definitions: match target must be a simple variable, got {:?}",
                other
            ),
        };
        for (pat, arm_body) in arms {
            bindings.push((matched_var.clone(), pat.clone()));
            walk(arm_body, bindings, out);
            bindings.pop();
        }
    } else {
        out.push(Branch {
            bindings: bindings.clone(),
            rhs: expr.clone(),
        });
    }
}

/// [KOR] 정의 주석 블록을 만듭니다. `funcs` 중 본문이 있고 값을 반환하는
///       함수만 다룹니다: 본문이 없는 함수(#[declare])는 보여줄 정의가
///       없고, Unit을 반환하는 함수(Lemma)의 본문은 정의가 아니라 증명
///       스크립트입니다 -- 백엔드 공리 생성과 같은 구분입니다.
/// [ENG] Builds the definitions comment block. Only bodied, value-returning
///       functions among `funcs` are shown: a bodiless function
///       (#[declare]) has no definition to show, and a Unit-returning
///       function (a lemma) has a proof script for a body, not a
///       definition -- the same distinction backend axiom generation makes.
pub fn print_definitions(program: &Program, funcs: &BTreeSet<String>) -> String {
    let mut lines: Vec<(String, String)> = Vec::new();
    for func in sorted_ci(funcs) {
        let def = program
            .functions
            .get(func)
            .unwrap_or_else(|| panic!("counterexample definitions: unknown function '{}'", func));
        let (_, out_type) = get_fun_types(&def.signature);
        if out_type == BaseType::Unit {
            continue;
        }
        let Some(body) = &def.body else {
            continue;
        };
        let params = param_names(&def.signature);
        for branch in decompose_body(body) {
            // [KOR] 브랜치 안에서 매칭된 파라미터는 곧 그 패턴입니다. 우변에
            //       남아 있는 매칭 파라미터(예: sub의 `Z => x`의 x)를 패턴으로
            //       치환해야 좌변과 같은 어휘로 읽힙니다: sub(S(x_min), Z) = S(x_min).
            // [ENG] Inside a branch, a matched parameter IS its pattern. A
            //       matched parameter surviving in the rhs (e.g. the x of
            //       sub's `Z => x` arm) is substituted by its pattern so the
            //       line reads in the same vocabulary as its left-hand side:
            //       sub(S(x_min), Z) = S(x_min).
            let subst: Vec<(Ident, String)> = branch
                .bindings
                .iter()
                .map(|(p, pat)| (p.clone(), render_pattern(pat)))
                .collect();
            lines.push((
                render_lhs(func, &params, &branch.bindings),
                render_expr(&branch.rhs, &subst),
            ));
        }
    }

    if lines.is_empty() {
        return String::new();
    }

    // [KOR] `=`를 세로로 맞추기 위해 가장 긴 좌변에 맞춰 패딩합니다.
    // [ENG] Pad to the longest left-hand side so the `=` column lines up.
    let width = lines.iter().map(|(lhs, _)| lhs.len()).max().unwrap();
    let mut out = String::from("; definitions:\n");
    for (lhs, rhs) in lines {
        out.push_str(&format!(";   {:<width$} = {}\n", lhs, rhs, width = width));
    }
    out
}

/// [KOR] 시그니처의 Arrow 사슬에서 파라미터 이름들을 뽑습니다.
/// [ENG] Extracts the parameter names from the signature's Arrow chain.
fn param_names(mut ty: &Type) -> Vec<Ident> {
    let mut names = Vec::new();
    while let Type::Arrow(f) = ty {
        names.push(f.param_name.clone());
        ty = &f.ret_type;
    }
    names
}

/// [KOR] 브랜치의 좌변을 만듭니다: 매칭된 파라미터는 패턴으로, 나머지는
///       이름 그대로. 예: `sub(S(x_min), Z)`.
/// [ENG] Builds the branch's left-hand side: matched parameters shown as
///       their patterns, the rest by name. E.g. `sub(S(x_min), Z)`.
fn render_lhs(func: &str, params: &[Ident], bindings: &[(Ident, Pattern)]) -> String {
    let rendered: Vec<String> = params
        .iter()
        .map(|p| {
            match bindings.iter().find(|(matched, _)| matched == p) {
                Some((_, pat)) => render_pattern(pat),
                None => p.clone(),
            }
        })
        .collect();
    format!("{}({})", func, rendered.join(", "))
}

fn render_pattern(pat: &Pattern) -> String {
    match pat {
        Pattern::Wildcard => "_".to_string(),
        Pattern::Ident(name) => name.clone(),
        Pattern::Constructor { name, args, .. } => {
            if args.is_empty() {
                variant_name(name).to_string()
            } else {
                let rendered: Vec<String> = args.iter().map(render_pattern).collect();
                format!("{}({})", variant_name(name), rendered.join(", "))
            }
        }
        Pattern::Tuple(_) => panic!("counterexample definitions: tuple patterns are not supported"),
    }
}

/// [KOR] 잎 표현식을 수학 표기로 렌더링합니다. If는 한 줄
///       `if c then a else b`로 인라인되고, `subst`에 있는 변수(매칭된
///       파라미터)는 그 패턴 표기로 바뀝니다.
/// [ENG] Renders a leaf expression in math notation. If is inlined as
///       `if c then a else b` on one line, and variables found in `subst`
///       (matched parameters) are replaced by their pattern rendering.
pub(super) fn render_expr(e: &Expr, subst: &[(Ident, String)]) -> String {
    match e {
        Expr::Var(name) => match subst.iter().find(|(p, _)| p == name) {
            Some((_, pat)) => pat.clone(),
            None => name.clone(),
        },
        Expr::BoolConst(b) => b.to_string(),
        Expr::Call { func, args } => render_application(func, args, subst),
        Expr::Constructor { name, args } => render_application(variant_name(name), args, subst),
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => format!(
            "if {} then {} else {}",
            render_expr(cond, subst),
            render_expr(then_expr, subst),
            render_expr(else_expr, subst)
        ),
        other => panic!(
            "counterexample definitions: expression cannot be rendered as a definition body: {:?}",
            other
        ),
    }
}

fn render_application(head: &str, args: &[Expr], subst: &[(Ident, String)]) -> String {
    if args.is_empty() {
        return head.to_string();
    }
    let rendered: Vec<String> = args.iter().map(|a| render_expr(a, subst)).collect();
    format!("{}({})", head, rendered.join(", "))
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap};

    use frontend::ast::{FunType, FunctionDef, Program};

    use super::*;

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn call(func: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            func: func.to_string(),
            args,
        }
    }

    fn cons(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Constructor {
            name: name.to_string(),
            args,
        }
    }

    fn pat_cons(name: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Constructor {
            name: name.to_string(),
            args,
            arg_types: None,
        }
    }

    fn pat_id(name: &str) -> Pattern {
        Pattern::Ident(name.to_string())
    }

    fn nat() -> BaseType {
        BaseType::Custom("Nat".to_string())
    }

    fn signature(params: &[(&str, BaseType)], ret: BaseType) -> Type {
        let mut ty = Type::Base(ret);
        for (name, p) in params.iter().rev() {
            ty = Type::Arrow(FunType {
                param_name: name.to_string(),
                param_type: Box::new(Type::Base(p.clone())),
                ret_type: Box::new(ty),
            });
        }
        ty
    }

    fn fun_def(params: &[(&str, BaseType)], ret: BaseType, body: Option<Expr>) -> FunctionDef {
        FunctionDef {
            signature: signature(params, ret),
            body,
            is_recursive: true,
        }
    }

    /// match x { Z => y, S(x_prime) => S(add(x_prime, y)) }
    fn add_body() -> Expr {
        Expr::Match {
            expr: Box::new(var("x")),
            arms: vec![
                (pat_cons("Nat::Z", vec![]), var("y")),
                (
                    pat_cons("Nat::S", vec![pat_id("x_prime")]),
                    cons("Nat::S", vec![call("add", vec![var("x_prime"), var("y")])]),
                ),
            ],
        }
    }

    /// match x { Z => Z, S(x_min) => match y { Z => x, S(y_min) => sub(x_min, y_min) } }
    fn sub_body() -> Expr {
        Expr::Match {
            expr: Box::new(var("x")),
            arms: vec![
                (pat_cons("Nat::Z", vec![]), cons("Nat::Z", vec![])),
                (
                    pat_cons("Nat::S", vec![pat_id("x_min")]),
                    Expr::Match {
                        expr: Box::new(var("y")),
                        arms: vec![
                            (pat_cons("Nat::Z", vec![]), var("x")),
                            (
                                pat_cons("Nat::S", vec![pat_id("y_min")]),
                                call("sub", vec![var("x_min"), var("y_min")]),
                            ),
                        ],
                    },
                ),
            ],
        }
    }

    #[test]
    fn decompose_flattens_nested_matches() {
        let branches = decompose_body(&sub_body());
        assert_eq!(branches.len(), 3);
        // Outermost binding first; the S-S branch carries both.
        assert_eq!(branches[2].bindings.len(), 2);
        assert_eq!(branches[2].bindings[0].0, "x");
        assert_eq!(branches[2].bindings[1].0, "y");
        assert!(matches!(&branches[2].rhs, Expr::Call { func, .. } if func == "sub"));
    }

    #[test]
    fn definitions_block_for_nat_arithmetic() {
        let mut functions = HashMap::new();
        functions.insert(
            "add".to_string(),
            fun_def(&[("x", nat()), ("y", nat())], nat(), Some(add_body())),
        );
        functions.insert(
            "sub".to_string(),
            fun_def(&[("x", nat()), ("y", nat())], nat(), Some(sub_body())),
        );
        let program = Program {
            datatypes: HashMap::new(),
            functions,
            goals: vec![],
        };
        let funcs: BTreeSet<String> = ["add", "sub"].iter().map(|s| s.to_string()).collect();

        // Widest left-hand side is "sub(S(x_min), S(y_min))" (23 chars);
        // every line must be padded to that column.
        let expected = String::from("; definitions:\n")
            + &line(23, "add(Z, y)", "y")
            + &line(23, "add(S(x_prime), y)", "S(add(x_prime, y))")
            + &line(23, "sub(Z, y)", "Z")
            + &line(23, "sub(S(x_min), Z)", "S(x_min)")
            + &line(23, "sub(S(x_min), S(y_min))", "sub(x_min, y_min)");
        assert_eq!(print_definitions(&program, &funcs), expected);
    }

    #[test]
    fn guarded_branch_renders_as_inline_if() {
        let nlist = BaseType::Custom("NList".to_string());
        // match xs { Nil => Z, Cons(h, t) =>
        //     if eq_nat(x, h) then S(count(x, t)) else count(x, t) }
        let count_body = Expr::Match {
            expr: Box::new(var("xs")),
            arms: vec![
                (pat_cons("NList::Nil", vec![]), cons("Nat::Z", vec![])),
                (
                    pat_cons("NList::Cons", vec![pat_id("h"), pat_id("t")]),
                    Expr::If {
                        cond: Box::new(call("eq_nat", vec![var("x"), var("h")])),
                        then_expr: Box::new(cons(
                            "Nat::S",
                            vec![call("count", vec![var("x"), var("t")])],
                        )),
                        else_expr: Box::new(call("count", vec![var("x"), var("t")])),
                    },
                ),
            ],
        };
        let mut functions = HashMap::new();
        functions.insert(
            "count".to_string(),
            fun_def(&[("x", nat()), ("xs", nlist)], nat(), Some(count_body)),
        );
        // A lemma (Unit return) and a bodiless declared function: both skipped.
        functions.insert(
            "some_lemma".to_string(),
            fun_def(&[("n", nat())], BaseType::Unit, Some(var("n"))),
        );
        functions.insert(
            "declared_fn".to_string(),
            fun_def(&[("n", nat())], nat(), None),
        );
        let program = Program {
            datatypes: HashMap::new(),
            functions,
            goals: vec![],
        };
        let funcs: BTreeSet<String> = ["count", "some_lemma", "declared_fn"]
            .iter()
            .map(|s| s.to_string())
            .collect();

        let expected = String::from("; definitions:\n")
            + &line(20, "count(x, Nil)", "Z")
            + &line(
                20,
                "count(x, Cons(h, t))",
                "if eq_nat(x, h) then S(count(x, t)) else count(x, t)",
            );
        assert_eq!(print_definitions(&program, &funcs), expected);
    }

    /// [KOR] 기대 문자열의 공백 수를 손으로 세지 않기 위한 한 줄 생성기.
    /// [ENG] One-line builder so expected strings don't rely on hand-counted spaces.
    fn line(width: usize, lhs: &str, rhs: &str) -> String {
        format!(";   {:<width$} = {}\n", lhs, rhs, width = width)
    }
}
