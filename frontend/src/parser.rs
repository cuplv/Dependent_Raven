use syn::{
    parse::{Parse, ParseStream, Result},
    punctuated::Punctuated,
    token, Expr as SynExpr, Ident as SynIdent, Token, Type as SynType,
};

use crate::ast::*;

/// 함수 인자 파싱: `name: ty` 또는 `name: ty{refinement}`
pub struct RefinedArg {
    pub name: SynIdent,
    pub colon_token: Token![:],
    pub ty: SynType,
    pub brace_token: Option<token::Brace>,
    pub refinement: Option<SynExpr>,
}

impl Parse for RefinedArg {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: SynIdent = input.parse()?;
        let colon_token: Token![:] = input.parse()?;
        let ty: SynType = input.parse()?;

        let mut brace_token = None;
        let mut refinement = None;

        // 인자 정제조건이 있는지 확인 (예: {x > 2})
        if input.peek(token::Brace) {
            let content;
            brace_token = Some(syn::braced!(content in input));
            refinement = Some(content.parse()?);
        }

        Ok(RefinedArg {
            name,
            colon_token,
            ty,
            brace_token,
            refinement,
        })
    }
}

/// 반환 타입 파싱: `r: MySet { ... }` 또는 `MySet`
pub struct SpecReturnType {
    pub bind: Option<(SynIdent, Token![:])>,
    pub ty: SynType,
    pub brace_token: Option<token::Brace>,
    pub refinement: Option<SynExpr>,
}

impl Parse for SpecReturnType {
    fn parse(input: ParseStream) -> Result<Self> {
        let bind = if input.peek(SynIdent) && input.peek2(Token![:]) {
            let ident: SynIdent = input.parse()?;
            let colon: Token![:] = input.parse()?;
            Some((ident, colon))
        } else {
            None
        };

        let ty: SynType = input.parse()?;

        let mut brace_token = None;
        let mut refinement = None;

        if input.peek(token::Brace) {
            let content;
            brace_token = Some(syn::braced!(content in input));
            refinement = Some(content.parse()?);
        }

        Ok(SpecReturnType {
            bind,
            ty,
            brace_token,
            refinement,
        })
    }
}

/// Lemma 파싱: `Lemma(requires(...), ensures(...))` 또는 `Lemma(...)`
pub struct SpecLemma {
    pub lemma_ident: SynIdent,
    pub paren_token: token::Paren,
    pub requires: Option<SynExpr>,
    pub ensures: SynExpr,
}

impl Parse for SpecLemma {
    fn parse(input: ParseStream) -> Result<Self> {
        let lemma_ident: SynIdent = input.parse()?;
        if lemma_ident.to_string() != "Lemma" {
            return Err(syn::Error::new(lemma_ident.span(), "Expected 'Lemma'"));
        }

        let content;
        let paren_token = syn::parenthesized!(content in input);
        
        let mut requires = None;
        let mut ensures = None;

        // 콤마로 구분된 여러 표현식이 올 수 있음
        let exprs = content.parse_terminated(SynExpr::parse, Token![,])?;
        
        for expr in exprs {
            if let SynExpr::Call(c) = &expr {
                if let SynExpr::Path(p) = &*c.func {
                    let func_name = p.path.segments.last().unwrap().ident.to_string();
                    if func_name == "requires" && c.args.len() == 1 {
                        requires = Some(c.args.first().unwrap().clone());
                        continue;
                    } else if func_name == "ensures" && c.args.len() == 1 {
                        ensures = Some(c.args.first().unwrap().clone());
                        continue;
                    }
                }
            }
            
            // 명시적 requires/ensures가 아니면 단독 사후 조건(ensures)으로 간주
            ensures = Some(expr);
        }

        let ensures = ensures.ok_or_else(|| syn::Error::new(lemma_ident.span(), "Lemma requires at least an ensures condition"))?;

        Ok(SpecLemma {
            lemma_ident,
            paren_token,
            requires,
            ensures,
        })
    }
}

pub enum SpecReturn {
    Type(SpecReturnType),
    Lemma(SpecLemma),
}

impl Parse for SpecReturn {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(SynIdent) && input.peek2(token::Paren) {
            // "Lemma(...)" 처럼 식별자 뒤에 괄호가 오는 경우 확인
            let fork = input.fork();
            let ident: SynIdent = fork.parse()?;
            if ident.to_string() == "Lemma" {
                return Ok(SpecReturn::Lemma(input.parse()?));
            }
        }
        
        Ok(SpecReturn::Type(input.parse()?))
    }
}

/// 함수/Lemma 시그니처 파싱: `(a: i32, b: i32{b > 0}) -> r: i32{r > a}`
pub struct SpecSignature {
    pub paren_token: token::Paren,
    pub inputs: Punctuated<RefinedArg, Token![,]>,
    pub rarrow_token: Token![->],
    pub ret: SpecReturn,
}

impl Parse for SpecSignature {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let paren_token = syn::parenthesized!(content in input);
        let inputs = content.parse_terminated(RefinedArg::parse, Token![,])?;

        let rarrow_token: Token![->] = input.parse()?;
        let ret: SpecReturn = input.parse()?;

        Ok(SpecSignature {
            paren_token,
            inputs,
            rarrow_token,
            ret,
        })
    }
}

// --- 아래부터는 syn 구조체를 우리 AST로 변환하는 헬퍼 함수들 ---

pub fn convert_base_type(ty: &SynType) -> BaseType {
    match ty {
        SynType::Path(p) => {
            let ident = p.path.segments.last().unwrap().ident.to_string();
            match ident.as_str() {
                "bool" | "Bool" => BaseType::Bool,
                "unit" | "Unit" => BaseType::Unit,
                _ => BaseType::Custom(ident), // Int, u32 등을 모두 Custom Sort로 취급
            }
        }
        SynType::Tuple(t) => {
            if t.elems.is_empty() {
                BaseType::Unit
            } else {
                let types = t.elems.iter().map(convert_base_type).collect();
                BaseType::Tuple(types)
            }
        }
        _ => unimplemented!("Unsupported base type: {:?}", ty),
    }
}

pub fn convert_expr(expr: &SynExpr) -> Expr {
    match expr {
        SynExpr::Lit(syn::ExprLit { lit, .. }) => match lit {
            syn::Lit::Bool(b) => Expr::BoolConst(b.value),
            other => panic!("unsupported syntax: literal `{}` (only `true`/`false`; numbers have no sort in the fragment)", quote::ToTokens::to_token_stream(other)),
        },
        SynExpr::Path(p) => {
            let ident = p.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::");
            let is_constructor = ident.contains("::") || ident.chars().next().unwrap_or('a').is_uppercase();
            if is_constructor {
                Expr::Constructor { name: ident, args: vec![] }
            } else {
                Expr::Var(ident)
            }
        }
        SynExpr::Binary(b) => {
            let op_call = match b.op {
                // 산술 및 비교 연산자는 EPR에서 미해석 함수 호출로 변환됨
                syn::BinOp::Add(_) => Some("add"),
                syn::BinOp::Sub(_) => Some("sub"),
                syn::BinOp::Mul(_) => Some("mul"),
                syn::BinOp::Lt(_) => Some("lt"),
                syn::BinOp::Le(_) => Some("le"),
                syn::BinOp::Gt(_) => Some("gt"),
                syn::BinOp::Ge(_) => Some("ge"),
                
                // 순수 논리 및 동치 연산자
                syn::BinOp::Eq(_) => return Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(convert_expr(&b.left)),
                    right: Box::new(convert_expr(&b.right)),
                },
                syn::BinOp::Ne(_) => return Expr::BinOp {
                    op: BinOp::Neq,
                    left: Box::new(convert_expr(&b.left)),
                    right: Box::new(convert_expr(&b.right)),
                },
                syn::BinOp::Or(_) => return Expr::BinOp {
                    op: BinOp::Or,
                    left: Box::new(convert_expr(&b.left)),
                    right: Box::new(convert_expr(&b.right)),
                },
                syn::BinOp::And(_) => return Expr::BinOp {
                    op: BinOp::And,
                    left: Box::new(convert_expr(&b.left)),
                    right: Box::new(convert_expr(&b.right)),
                },
                _ => None,
            };

            if let Some(func_name) = op_call {
                Expr::Call {
                    func: func_name.to_string(),
                    args: vec![convert_expr(&b.left), convert_expr(&b.right)],
                }
            } else {
                panic!("unsupported syntax: binary operator `{}`", quote::ToTokens::to_token_stream(&b.op))
            }
        }
        SynExpr::Unary(u) => {
            if let syn::UnOp::Deref(_) = u.op {
                // Rust의 메모리 참조 해제(*) 기호는 논리적 증명 단계에서는 무시해도 됩니다.
                return convert_expr(&u.expr);
            }
            
            let op = match u.op {
                syn::UnOp::Not(_) => UnOp::Not,
                _ => panic!("unsupported syntax: unary operator `{}`", quote::ToTokens::to_token_stream(&u.op)),
            };
            Expr::UnOp {
                op,
                expr: Box::new(convert_expr(&u.expr)),
            }
        }
        SynExpr::Call(c) => {
            if let SynExpr::Path(p) = &*c.func {
                let segments: Vec<_> = p.path.segments.iter().map(|s| s.ident.to_string()).collect();
                let func = segments.join("::");

                // forall(...) 또는 exists(...) 처리
                if (func == "forall" || func == "exists") && c.args.len() == 1 {
                    if let syn::Expr::Closure(closure) = c.args.first().unwrap() {
                        let mut binders = Vec::new();
                        for arg in &closure.inputs {
                            if let syn::Pat::Type(pt) = arg {
                                if let syn::Pat::Ident(pi) = &*pt.pat {
                                    let ident = pi.ident.to_string();
                                    let base_type = convert_base_type(&pt.ty);
                                    binders.push((ident, base_type));
                                } else {
                                    panic!("unsupported syntax: quantifier binder must be a plain name, got `{}`", quote::ToTokens::to_token_stream(pt));
                                }
                            } else {
                                panic!("unsupported syntax: quantifier binder `{}` needs a type annotation (`|x: T| ..`)", quote::ToTokens::to_token_stream(arg));
                            }
                        }
                        let body = Box::new(convert_expr(&closure.body));
                        return if func == "forall" {
                            Expr::Forall { binders, body }
                        } else {
                            Expr::Exists { binders, body }
                        };
                    }
                }
                
                // Box::new 처리: 증명 로직에서는 메모리 할당(Box)을 무시하고 내부 값만 취급합니다.
                if segments == vec!["Box", "new"] && c.args.len() == 1 {
                    return convert_expr(c.args.first().unwrap());
                }
                
                // Rust 문법의 한계로 => 를 바로 쓸 수 없으므로 implies(p, q) 함수 호출로 우회 지원
                if func == "implies" && c.args.len() == 2 {
                    let mut args = c.args.iter();
                    return Expr::BinOp {
                        op: BinOp::Implies,
                        left: Box::new(convert_expr(args.next().unwrap())),
                        right: Box::new(convert_expr(args.next().unwrap())),
                    };
                }
                
                let args = c.args.iter().map(convert_expr).collect();

                // 생성자(Constructor)와 일반 함수(Call) 구분
                let is_constructor = func.contains("::") || func.chars().next().unwrap_or('a').is_uppercase();

                if is_constructor {
                    Expr::Constructor { name: func, args }
                } else {
                    Expr::Call { func, args }
                }
            } else {
                panic!("unsupported syntax: call of a non-path expression `{}`", quote::ToTokens::to_token_stream(&c.func))
            }
        }
        SynExpr::Closure(closure) => {
            // 클로저 자체를 Expr로 변환할 때는 일단 바디만 변환 (양화사 내부에서 처리됨)
            convert_expr(&closure.body)
        }
        SynExpr::MethodCall(m) => {
            if m.method == "clone" {
                // Rust의 소유권 때문에 붙인 .clone() 메서드는 증명 로직에서는 완전히 무시해도 됩니다.
                return convert_expr(&m.receiver);
            }
            // 지원하지 않는 메서드 호출은 일단 변수로 처리 (검증에 쓰이지 않는 본문용)
            panic!("unsupported syntax: method call `.{}(..)` (only `.clone()`)", m.method)
        }
        SynExpr::Tuple(t) => {
            let exprs = t.elems.iter().map(convert_expr).collect();
            Expr::Tuple(exprs)
        }
        SynExpr::If(i) => {
            let cond = Box::new(convert_expr(&i.cond));
            
            // [KOR] `then` 브랜치: Block 전체를 Expr로 변환하도록 수정하여 내부의 instantiate!를 보존합니다.
            // [ENG] Convert the entire `then` block to Expr to preserve internal instantiate! macros.
            let then_block_expr = SynExpr::Block(syn::ExprBlock { attrs: vec![], label: None, block: i.then_branch.clone() });
            let then_expr = Box::new(convert_expr(&then_block_expr));

            // `else` 브랜치 파싱
            let else_expr = Box::new(if let Some((_, else_branch)) = &i.else_branch {
                convert_expr(else_branch)
            } else {
                Expr::Tuple(vec![])
            });

            Expr::If { cond, then_expr, else_expr }
        }
        SynExpr::Let(l) => {
            Expr::Let {
                pat: convert_pattern(&l.pat),
                bound_expr: Box::new(convert_expr(&l.expr)),
                body: Box::new(Expr::Tuple(vec![])), // 실제 body는 스코프 안에서 조립됨
            }
        }
        SynExpr::Match(m) => {
            // A match target must be a variable (the checker's path condition
            // and the backend's axiom generation both assume it). A scrutinee
            // that is anything else -- a call, or a tuple with a call inside --
            // is let-bound to a fresh `_scrut_N` in front of the match, so
            // `match (eval(a), eval(b)) { .. }` reads as written.
            let mut scrutinee_lets: Vec<(Ident, Expr)> = Vec::new();
            let mut bind_if_needed = |e: Expr| -> Expr {
                match e {
                    Expr::Var(_) => e,
                    other => {
                        let name = fresh_name("_scrut");
                        scrutinee_lets.push((name.clone(), other));
                        Expr::Var(name)
                    }
                }
            };
            let target = match convert_expr(&m.expr) {
                Expr::Tuple(components) => {
                    Expr::Tuple(components.into_iter().map(&mut bind_if_needed).collect())
                }
                other => bind_if_needed(other),
            };
            let expr = Box::new(target);
            let arms = m.arms.iter().map(|arm| {
                // A guard would have to become an extra path condition on this arm
                // AND its negation on every later arm (first-match semantics); arms
                // are encoded as unordered cases today, so a dropped guard yields
                // overlapping definitional axioms. Reject rather than mis-encode.
                if arm.guard.is_some() {
                    panic!(
                        "match guards (`pat if cond =>`) are not supported; \
                         move the condition into the arm body as an `if`"
                    );
                }
                let pat = convert_pattern(&arm.pat);
                // A bare `_` arm is a catch-all; arms are encoded as unordered
                // cases, so it would overlap every other arm. It stays a
                // `Wildcard` here and resolve.rs replaces it, once the datatypes
                // are known, by the constructors the earlier arms leave uncovered.
                let pat = match pat {
                    Pattern::Wildcard => pat,
                    other => name_nested_wildcards(other),
                };
                let body = convert_expr(&arm.body);
                (pat, body)
            }).collect();

            // let _scrut_0 = e0 in let _scrut_1 = e1 in match (_scrut_0, _scrut_1) { .. }
            scrutinee_lets.into_iter().rev().fold(Expr::Match { expr, arms }, |body, (name, bound)| {
                Expr::Let {
                    pat: Pattern::Ident(name),
                    bound_expr: Box::new(bound),
                    body: Box::new(body),
                }
            })
        }
        SynExpr::Paren(p) => convert_expr(&p.expr),
        SynExpr::Block(b) => convert_block(&b.block),
        SynExpr::Macro(m) => {
            let mac_name = m.mac.path.segments.last().unwrap().ident.to_string();
            
            if mac_name == "instantiate" {
                if let Ok(inner_expr) = syn::parse2::<syn::Expr>(m.mac.tokens.clone()) {
                    return Expr::Instantiate(Box::new(convert_expr(&inner_expr)));
                }
            }
            
            if mac_name == "forall" || mac_name == "exists" {
                if let Ok(closure) = syn::parse2::<syn::ExprClosure>(m.mac.tokens.clone()) {
                    let mut binders = Vec::new();
                    for arg in closure.inputs {
                        if let syn::Pat::Type(pt) = arg {
                            if let syn::Pat::Ident(pi) = &*pt.pat {
                                binders.push((pi.ident.to_string(), convert_base_type(&pt.ty)));
                            }
                        }
                    }
                    let body = Box::new(convert_expr(&closure.body));
                    return if mac_name == "forall" {
                        Expr::Forall { binders, body }
                    } else {
                        Expr::Exists { binders, body }
                    };
                }
            }
            panic!("unsupported syntax: macro `{}!` in an expression", mac_name)
        }
        other => panic!("unsupported syntax: expression `{}`", quote::ToTokens::to_token_stream(other)),
    }
}

/// Converts a block `{ s1; s2; ...; tail }` into a chain of `Let` bindings.
///
/// A block is a sequence of statements followed by an optional tail expression,
/// and its meaning is exactly sequential binding: each statement is evaluated,
/// its result is bound (to a name for `let` statements, to nothing for bare
/// expression statements), and the rest of the block continues under that
/// binding. We therefore translate
///
/// ```text
/// { let y = e1;  e2();  tail }   ==>   Let { y, e1, Let { _, e2(), tail } }
/// ```
///
/// A final statement WITHOUT a trailing semicolon is the block's value (the
/// tail). If the block ends with a semicolon-terminated statement, or has no
/// statements at all, its value is the unit value, so the chain ends in an
/// empty tuple. A block that is just `{ tail }` translates to the tail alone -
/// no `Let` nodes are introduced.
///
/// `instantiate!(term)` in statement position records a proof hint; it is a
/// unit-valued statement like any other and becomes an ordinary binding link.
///
/// Unsupported statement forms (`let` without an initializer, `let ... else`,
/// nested item definitions, unknown statement macros) are rejected with a
/// panic rather than skipped: silently ignoring a statement would make the
/// verifier reason about a different program than the one on screen.
fn convert_block(block: &syn::Block) -> Expr {
    // Bound statements, in source order, plus the optional tail expression.
    let mut links: Vec<(Pattern, Expr)> = Vec::new();
    let mut tail: Expr = Expr::Tuple(vec![]);
    let count = block.stmts.len();

    for (idx, stmt) in block.stmts.iter().enumerate() {
        let is_last = idx + 1 == count;
        match stmt {
            // `let <pat> = <expr>;`
            syn::Stmt::Local(local) => {
                let init = match &local.init {
                    Some(init) => init,
                    None => panic!(
                        "`let` bindings without an initializer are not supported in verified bodies"
                    ),
                };
                if init.diverge.is_some() {
                    panic!("`let ... else` is not supported in verified bodies");
                }
                links.push((convert_pattern(&local.pat), convert_expr(&init.expr)));
            }
            // An expression statement. In the last position without a trailing
            // semicolon it is the block's value; otherwise its value is bound
            // to nothing and the block continues after it.
            syn::Stmt::Expr(e, semi) => {
                if is_last && semi.is_none() {
                    tail = convert_expr(e);
                } else {
                    links.push((Pattern::Wildcard, convert_expr(e)));
                }
            }
            // A macro invocation in statement position.
            syn::Stmt::Macro(m) => {
                let mac_name = m.mac.path.segments.last().unwrap().ident.to_string();
                if mac_name == "instantiate" {
                    match syn::parse2::<syn::Expr>(m.mac.tokens.clone()) {
                        Ok(inner) => links.push((
                            Pattern::Wildcard,
                            Expr::Instantiate(Box::new(convert_expr(&inner))),
                        )),
                        Err(err) => {
                            panic!("failed to parse the argument of instantiate!(..): {}", err)
                        }
                    }
                } else {
                    panic!(
                        "unsupported statement macro `{}!` in a verified body",
                        mac_name
                    );
                }
            }
            syn::Stmt::Item(_) => {
                panic!("nested item definitions are not supported in verified bodies");
            }
        }
    }

    // Assemble the chain from the inside out: the last binding wraps the tail.
    links
        .into_iter()
        .rev()
        .fold(tail, |body, (pat, bound)| Expr::Let {
            pat,
            bound_expr: Box::new(bound),
            body: Box::new(body),
        })
}

thread_local! {
    static WILDCARD_COUNTER: std::cell::Cell<usize> = std::cell::Cell::new(0);
}

/// Replaces every `_` nested inside a constructor or tuple pattern with a fresh
/// `_wild_N` binder. A field wildcard is just a binder nobody reads, but the
/// checker needs a name to state the path condition `x == C(.., _wild_N, ..)`
/// and the backend needs one for the axiom's quantifier. Names are unique per
/// process so nested matches in one body never produce duplicate binders.
/// Only match-arm patterns go through here; `let _ = e;` keeps its wildcard.
/// A name no source program uses, unique per process: `_wild_N` for the
/// fields of a wildcard pattern, `_scrut_N` for a let-bound match scrutinee.
pub(crate) fn fresh_name(prefix: &str) -> Ident {
    let n = WILDCARD_COUNTER.with(|c| {
        let n = c.get();
        c.set(n + 1);
        n
    });
    format!("{}_{}", prefix, n)
}

pub(crate) fn name_nested_wildcards(pat: Pattern) -> Pattern {
    match pat {
        Pattern::Wildcard => Pattern::Ident(fresh_name("_wild")),
        Pattern::Constructor { name, args, arg_types } => Pattern::Constructor {
            name,
            args: args.into_iter().map(name_nested_wildcards).collect(),
            arg_types,
        },
        Pattern::Tuple(args) => {
            Pattern::Tuple(args.into_iter().map(name_nested_wildcards).collect())
        }
        other => other,
    }
}

pub fn convert_pattern(pat: &syn::Pat) -> Pattern {
    match pat {
        syn::Pat::Wild(_) => Pattern::Wildcard,
        syn::Pat::Ident(pi) => {
            // `name @ subpattern` binds the name but the subpattern's shape and
            // binders would be lost; reject rather than silently widen the arm.
            if pi.subpat.is_some() {
                panic!(
                    "`name @ pattern` bindings are not supported; \
                     match on the constructor pattern directly"
                );
            }
            Pattern::Ident(pi.ident.to_string())
        }
        // A type-annotated pattern, e.g. `let y: Nat = ...`. The annotation adds
        // no information the checker doesn't already infer from the initializer,
        // so only the inner pattern matters here.
        syn::Pat::Type(pt) => convert_pattern(&pt.pat),
        syn::Pat::TupleStruct(pts) => {
            let ident = pts.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::");
            let args = pts.elems.iter().map(convert_pattern).collect();
            Pattern::Constructor { name: ident, args, arg_types: None }
        }
        syn::Pat::Tuple(pt) => {
            let args = pt.elems.iter().map(convert_pattern).collect();
            Pattern::Tuple(args)
        }
        syn::Pat::Path(pp) => {
            let ident = pp.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::");
            Pattern::Constructor { name: ident, args: vec![], arg_types: None }
        }
        // A `bool` literal in a pattern is written as the pseudo-constructor
        // `bool::true` / `bool::false`. It never reaches the checker or the
        // backend: resolve.rs compiles any match containing one into an `if`
        // on the matched value (see `compile_rows`).
        syn::Pat::Lit(syn::PatLit { lit: syn::Lit::Bool(b), .. }) => Pattern::Constructor {
            name: format!("bool::{}", b.value),
            args: vec![],
            arg_types: None,
        },
        syn::Pat::Lit(other) => panic!(
            "unsupported syntax: literal pattern `{}` (only `true`/`false`)",
            quote::ToTokens::to_token_stream(other)
        ),
        _ => unimplemented!("Unsupported pattern: {:?}", pat),
    }
}

pub fn convert_signature(spec: SpecSignature) -> Type {
    let mut requires_clause: Option<Expr> = None;

    let mut current_type = match spec.ret {
        SpecReturn::Type(ret_info) => {
            let ret_base = convert_base_type(&ret_info.ty);
            if let Some(refinement) = ret_info.refinement {
                Type::Refined(RefinedType {
                    bound_var: ret_info.bind.unwrap().0.to_string(),
                    base: ret_base,
                    predicate: convert_expr(&refinement),
                })
            } else {
                Type::Base(ret_base)
            }
        },
        SpecReturn::Lemma(lemma_info) => {
            // [KOR] Lemma(증명)는 Unit을 반환하고 ensures를 사후 조건으로 갖는 순수 함수로 취급(Desugaring)됩니다.
            //       requires(사전 조건)는 나중에 제일 마지막 인자의 정제 조건(Refinement)으로 밀어 넣기 위해 임시 저장합니다.
            // [ENG] Lemma is desugared into a pure function returning Unit with 'ensures' as the postcondition.
            //       'requires' is temporarily stored to be injected into the refinement of the last argument.
            if let Some(req) = lemma_info.requires {
                requires_clause = Some(convert_expr(&req));
            }
            
            let ensures = convert_expr(&lemma_info.ensures);
            Type::Refined(RefinedType {
                bound_var: "_ret".to_string(),
                base: BaseType::Unit,
                predicate: ensures,
            })
        }
    };

    let inputs: Vec<_> = spec.inputs.into_iter().collect();
    
    // 인자가 하나도 없는데 requires가 있으면 오류를 냅니다. (어디에 붙일 곳이 없으므로)
    if inputs.is_empty() && requires_clause.is_some() {
        panic!("A Lemma with a 'requires' clause must have at least one argument to attach the precondition to.");
    }

    for (i, arg) in inputs.iter().rev().enumerate() {
        let param_name = arg.name.to_string();
        let param_base = convert_base_type(&arg.ty);
        
        let mut param_type = if let Some(refinement) = &arg.refinement {
            Type::Refined(RefinedType {
                bound_var: param_name.clone(), 
                base: param_base.clone(),
                predicate: convert_expr(refinement),
            })
        } else {
            Type::Base(param_base.clone())
        };

        // [KOR] 가장 마지막 인자(역순 순회이므로 첫 번째 순회(i == 0))에 requires 조건을 주입합니다!
        // [ENG] Inject the 'requires' condition into the refinement of the last argument (first in the reversed iteration).
        if i == 0 {
            if let Some(req) = requires_clause.take() {
                param_type = match param_type {
                    Type::Base(b) => Type::Refined(RefinedType {
                        bound_var: param_name.clone(),
                        base: b,
                        predicate: req,
                    }),
                    Type::Refined(mut r) => {
                        // 기존 조건과 requires 조건을 AND로 묶습니다.
                        r.predicate = Expr::BinOp {
                            op: BinOp::And,
                            left: Box::new(r.predicate),
                            right: Box::new(req),
                        };
                        Type::Refined(r)
                    }
                    _ => unreachable!(),
                };
            }
        }

        current_type = Type::Arrow(FunType {
            param_name,
            param_type: Box::new(param_type),
            ret_type: Box::new(current_type),
        });
    }

    current_type
}
