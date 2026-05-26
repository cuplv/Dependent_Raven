use crate::ast::{Program, FunctionDef, Goal, Type, Expr, Ident, BaseType, BinOp};
use crate::parser::{SpecSignature, convert_signature, convert_expr};
use syn::{ItemFn, ItemEnum, Type as SynType, PathArguments, GenericArgument};

/// [KOR] #[define] 열거형 등록: 귀납적 데이터 타입(Enum)을 파싱하여 Program의 datatypes에 등록합니다.
///       재귀 타입 지정을 위해 사용된 Box<T> 구조에서 T를 추출하는 과정을 포함합니다.
/// [ENG] Register #[define] enum: Parses inductive datatypes and registers them in Program's datatypes.
///       Includes logic to extract T from Box<T> used for recursive type definitions.
pub fn register_enum(program: &mut Program, enum_name: &str, enum_str: &str) {
    println!(" [API] Registering #[define] enum: {}", enum_name);
    
    let item_enum: ItemEnum = syn::parse_str(enum_str).expect("Failed to parse declared enum");
    
    let mut constructors = Vec::new();
    for variant in item_enum.variants {
        let con_name = variant.ident.to_string();
        let mut arg_types = Vec::new();
        
        match variant.fields {
            syn::Fields::Unnamed(fields) => {
                for field in fields.unnamed {
                    // Extract the inner type if it's wrapped in Box<T>
                    let ty_str = if let SynType::Path(type_path) = &field.ty {
                        let last_segment = type_path.path.segments.last().unwrap();
                        if last_segment.ident == "Box" {
                            if let PathArguments::AngleBracketed(args) = &last_segment.arguments {
                                if let Some(GenericArgument::Type(SynType::Path(inner_path))) = args.args.first() {
                                    inner_path.path.segments.last().unwrap().ident.to_string()
                                } else {
                                    panic!("Expected type path inside Box")
                                }
                            } else {
                                panic!("Expected angle bracketed arguments for Box")
                            }
                        } else {
                            last_segment.ident.to_string()
                        }
                    } else {
                        panic!("Unsupported type in enum variant")
                    };
                    
                    arg_types.push(BaseType::Custom(ty_str));
                }
            }
            syn::Fields::Unit => {
                // No arguments for this constructor
            }
            syn::Fields::Named(_) => panic!("Named fields are not supported in Ravencheck enums"),
        }
        
        constructors.push((con_name, arg_types));
    }
    
    program.datatypes.insert(enum_name.to_string(), constructors);
}

/// [KOR] #[declare] 함수 등록: 본문은 완전히 무시하고 시그니처만 추출하여 저장합니다.
/// [ENG] Register #[declare] function: Completely ignores the body and extracts only the signature.
pub fn register_declare(program: &mut Program, fn_name: &str, fn_str: &str) {
    println!(" [API] Registering #[declare] function: {}", fn_name);
    
    let item_fn: ItemFn = syn::parse_str(fn_str).expect("Failed to parse declared function");
    
    // Rust의 기본 함수 선언에서 시그니처 정보를 추출하여 Type AST로 변환하는 과정이 필요합니다.
    // 현재는 간단하게 플레이스홀더 타입을 넣거나, 향후 전용 파서를 연결할 수 있습니다.
    // 여기선 일단 이름만 등록해 둡니다.
}

fn extract_signature_from_fn(item_fn: &ItemFn) -> Type {
    let mut current_type = match &item_fn.sig.output {
        syn::ReturnType::Default => Type::Base(BaseType::Unit),
        syn::ReturnType::Type(_, ty) => Type::Base(crate::parser::convert_base_type(ty)),
    };

    for arg in item_fn.sig.inputs.iter().rev() {
        if let syn::FnArg::Typed(pat_type) = arg {
            if let syn::Pat::Ident(pat_ident) = &*pat_type.pat {
                let param_name = pat_ident.ident.to_string();
                let param_base = crate::parser::convert_base_type(&pat_type.ty);
                current_type = Type::Arrow(crate::ast::FunType {
                    param_name,
                    param_type: Box::new(Type::Base(param_base)),
                    ret_type: Box::new(current_type),
                });
            } else {
                panic!("Only ident patterns are supported in inferred signatures");
            }
        } else {
            panic!("Self arguments are not supported");
        }
    }
    current_type
}

/// [KOR] #[val] 및 #[lemma] 함수 등록: 
///       시그니처가 없으면 Rust AST에서 추론하며, 본문(body)이 있으면 무조건 typecheck_expr를 태워서 VC를 생성합니다.
///       이제 Lemma도 단순한 함수 타입(Unit 반환)으로 처리되므로, 모든 증명과 함수가 동일한 파이프라인을 탑니다!
pub fn register_val(program: &mut Program, fn_name: &str, sig_str: Option<&str>, fn_str: &str, is_recursive: bool) {
    println!(" [API] Registering function (or lemma): {}", fn_name);
    
    let item_fn: ItemFn = syn::parse_str(fn_str).expect("Failed to parse declared function");
    
    let type_sig = if let Some(s) = sig_str {
        let parsed_sig: SpecSignature = syn::parse_str(s).expect("Failed to parse signature");
        convert_signature(parsed_sig)
    } else {
        extract_signature_from_fn(&item_fn)
    };
    
    let block_expr = syn::Expr::Block(syn::ExprBlock {
        attrs: vec![],
        label: None,
        block: *item_fn.block.clone(),
    });
    let body_expr = convert_expr(&block_expr);

    // 환경에 함수 먼저 등록 (재귀 호출 대비)
    program.functions.insert(fn_name.to_string(), FunctionDef {
        signature: type_sig.clone(),
        body: Some(body_expr.clone()), 
        is_recursive,
    });
    
    // 만약 본문이 비어있지 않다면(의미 있는 로직이 있다면) 타입 체킹(증명) 수행
    let mut env = crate::env::TypeEnv::new();
    let mut vcs = Vec::new();
    
    // =========================================================================
    // [T-FUN] / [T-ABS] Rule: Function Abstraction
    // =========================================================================
    // [KOR] AST에 람다 노드가 없으므로, 최상위 함수 등록 시점에서 T-FUN을 처리합니다.
    // [ENG] Since there is no Lambda node in the AST, we handle T-FUN at top-level function registration.
    env.with_scope(|inner_env| {
        let mut current_sig = type_sig.clone();
        
        // -----------------------------------------------------------------
        // PREMISE 1: \Gamma, x:\tau_x (Extending the Environment)
        // -----------------------------------------------------------------
        // [KOR] 함수의 시그니처(Arrow 타입)를 순회하며 파라미터들을 환경에 등록합니다.
        //       이는 "함수 내부를 검사할 때는 인자가 조건을 만족한 채로 들어온다"고 가정(Assume)하는 것입니다.
        // [ENG] Iterate through the function signature (Arrow type) and register parameters to the environment.
        //       This assumes that "inside the function, arguments perfectly satisfy their preconditions".
        while let Type::Arrow(fun_type) = current_sig {
            // [KOR] 파라미터 이름과 타입을 환경에 바인딩
            // [ENG] Bind the parameter name and its type into the environment
            inner_env.insert_var(fun_type.param_name.clone(), *fun_type.param_type.clone());
            
            // [KOR] 다음 화살표(또는 최종 반환 타입)로 이동
            // [ENG] Move to the next arrow (or final return type)
            current_sig = *fun_type.ret_type;
        }
        
        // -----------------------------------------------------------------
        // PREMISE 2: \vdash e : \tau_{out} (Checking the Body)
        // -----------------------------------------------------------------
        // [KOR] 파라미터가 모두 등록된 환경(inner_env)에서, 최종 반환 타입(current_sig)을 
        //       목표(Expected)로 삼아 함수의 바디(body_expr)를 하향식으로 검사합니다.
        // [ENG] In the environment where all parameters are registered (inner_env), check the function's 
        //       body top-down against the final return type (current_sig) as the Expected type.
        crate::typechecking::check_expr(inner_env, &body_expr, &current_sig, &program.functions, &mut vcs);
        
        // -----------------------------------------------------------------
        // CONSEQUENCE: \Gamma \vdash (\lambda x:\tau_x. e) : (x:\tau_x) \to \tau_{out}
        // -----------------------------------------------------------------
        // [KOR] check_expr가 무사히 vcs에 논리식을 담아주면, 이 함수 전체의 타입 체킹이 논리적으로 성립합니다.
        // [ENG] If `check_expr` successfully accumulates VCs, the type checking for this entire function holds logically.
    });

    // println!("  ✅ Generated VCs for {}: {} items", fn_name, vcs.len());
    // for (i, vc) in vcs.iter().enumerate() {
    //     println!("     [Raw VC {}]:\n{:#?}", i, vc);
    // }

    if !vcs.is_empty() {
        let mut combined_vc = vcs[0].clone();
        for vc in &vcs[1..] {
            combined_vc = Expr::BinOp {
                op: BinOp::And,
                left: Box::new(combined_vc),
                right: Box::new(vc.clone()),
            };
        }
        
        // [KOR] 사용자가 명시적인 타입 시그니처(Lemma 또는 Refinement)를 제공했을 때만 SMT 솔버의 목표(Goal)로 등록합니다.
        //       단순히 `#[val]`만 적힌 일반 함수는 VC가 생성되더라도 (예: Trivial VC) 검증을 생략합니다.
        if sig_str.is_some() {
            program.goals.push(Goal {
                name: fn_name.to_string(),
                property: combined_vc,
            });
        }
    }
}

/// [KOR] #[lemma] 매크로의 하위 호환성을 위해 register_val로 라우팅합니다.
pub fn register_lemma(program: &mut Program, fn_name: &str, sig_str: Option<&str>, fn_str: &str, is_recursive: bool) {
    register_val(program, fn_name, sig_str, fn_str, is_recursive);
}
