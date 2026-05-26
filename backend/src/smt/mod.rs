pub mod solver;
pub mod axioms;
pub mod builder;

use std::env;
use std::fs;

use frontend::ast::{Program, Type, BaseType, Expr, UnOp};
use crate::anf::{transform_expr as anf_transform, NameGenerator};
use crate::nnf::{transform_expr as nnf_transform};
use crate::relabs::{transform_expr as relabs_transform};
use crate::epr_check::{check_for_cycles, render_cycle};
use crate::smt::solver::SolverConfig;
use crate::smt::builder::{expr_to_smt, render_sort, sanitize_id};
use crate::smt::axioms::{functionality_axiom, injectivity_axiom, disjointness_axiom};

/// [KOR] 함수의 시그니처에서 인자 타입 목록과 반환 타입을 추출합니다.
/// [ENG] Extracts the list of argument types and the return type from a function's signature.
fn get_fun_types(mut ty: &Type) -> (Vec<BaseType>, BaseType) {
    let mut inputs = Vec::new();
    while let Type::Arrow(f) = ty {
        let base = match &*f.param_type {
            Type::Base(b) => b.clone(),
            Type::Refined(r) => r.base.clone(),
            _ => panic!("Complex param types not supported in backend"),
        };
        inputs.push(base);
        ty = &*f.ret_type;
    }
    let output = match ty {
        Type::Base(b) => b.clone(),
        Type::Refined(r) => r.base.clone(),
        _ => panic!("Complex return types not supported in backend"),
    };
    (inputs, output)
}

/// 백엔드 컴파일러 파이프라인 진입점
/// [KOR] Program 객체를 받아 각 목표(Goal)에 대해 파이프라인을 순차적으로 수행합니다.
///       RAVENCHECK_DUMP_IR 환경 변수가 설정된 경우 중간 변환 결과(IR)를 logs 폴더에 파일로 저장합니다.
pub fn encode_and_solve(program: Program) -> Result<(), String> {
    println!("\n⛓️ [Backend] Starting Pipeline for {} goals...", program.goals.len());
    
    // 1. 디버깅 플래그 확인 (RAVENCHECK_DUMP_IR)
    let dump_ir = env::var("RAVENCHECK_DUMP_IR").is_ok();
    if dump_ir {
        let _ = fs::create_dir_all("logs");
    }
    
    let mut relabs_goals = Vec::new();
    for goal in &program.goals {
        // [증명을 위한 핵심]: 목표 명제가 '항상 참'인지 증명하기 위해, 
        // 목표 명제의 '부정(Not)'이 '만족 불가능(Unsat)'인지 솔버에게 묻습니다.
        let negated_goal = Expr::UnOp {
            op: UnOp::Not,
            expr: Box::new(goal.property.clone()),
        };

        // 1. ANF 변환 수행
        let mut gen = NameGenerator::new();
        let anf_expr = anf_transform(&negated_goal, &mut gen);
        
        // 2. NNF 변환 수행
        let nnf_expr = nnf_transform(anf_expr.clone());
        
        // 3. Relational Abstraction 수행
        let relabs_expr = relabs_transform(&nnf_expr, &program.functions);
        
        if dump_ir {
            let write_log = |step: &str, content: String| {
                let filename = format!("logs/{}_{}.log", goal.name, step);
                if let Err(e) = fs::write(&filename, content) {
                    println!("   ⚠️ Failed to write log {}: {}", filename, e);
                }
            };

            write_log("0_raw_vc_negated", format!("{:#?}", negated_goal));
            write_log("1_anf", format!("{:#?}", anf_expr));
            write_log("2_nnf", format!("{:#?}", nnf_expr));
            write_log("3_relabs", format!("{:#?}", relabs_expr));
            
            println!("  💾 Saved IR logs to `logs/{}_*.log`", goal.name);
        }
        relabs_goals.push((goal.name.clone(), relabs_expr));
    }

    // 2. EPR 프래그먼트 검사 (Sort Cycle Check) - RelAbs 이후에 수행!
    let goals_for_check: Vec<_> = relabs_goals.iter().map(|(_, expr)| expr.clone()).collect();
    if let Err(cycles) = check_for_cycles(&goals_for_check, &program.functions) {
        let mut err_msg = String::from("Found Sort Cycles! This breaks decidability.\n");
        for c in cycles {
            err_msg.push_str(&format!("   Cycle: {}\n", render_cycle(&c)));
        }
        return Err(err_msg);
    } else {
        println!("✅ [EPR Check Passed] No sort cycles detected. Logic is decidable.");
    }

    // 3. SMT 인코딩 및 실행
    let mut config = SolverConfig::default();
    
    // 로그 폴더가 없으면 미리 생성합니다.
    let _ = fs::create_dir_all("logs");
    
    for (goal_name, relabs_expr) in relabs_goals {
        println!("🎯 Solving Goal: {}", goal_name);

        // 무조건 .smt2 파일에 로그를 남기도록 설정합니다.
        let smt_log_path = format!("logs/{}_failed_query.smt2", goal_name);
        config.set_log_file(smt_log_path.clone());
        
        let mut builder = config.context_builder();
        let mut ctx = builder.build().expect("Failed to build SMT context");
        ctx.set_logic("ALL").unwrap();

        // [KOR] Unit 소트 선언 (프론트엔드에서 넘어올 수 있으므로)
        ctx.declare_sort("Unit", 0).unwrap();
        ctx.declare_const("unit_val", ctx.atom("Unit")).unwrap();

        // 3.1. 소트(Sort) 선언
        for (enum_name, _) in &program.datatypes {
            let sort_name = render_sort(&BaseType::Custom(enum_name.clone()));
            ctx.declare_sort(sort_name, 0).unwrap();
        }

        // 3.2. 데이터 생성자 (Constructors) 및 공리 선언
        for (enum_name, variants) in &program.datatypes {
            let out_type = BaseType::Custom(enum_name.clone());
            for (cons_name, arg_types) in variants {
                // RelAbs 단계에서 생성자는 `{enum_name}::{cons_name}_rel` 형태로 변환됨
                let rel_name = sanitize_id(&format!("{}::{}_rel", enum_name, cons_name)); 
                
                let mut smt_args = Vec::new();
                for ty in arg_types {
                    smt_args.push(ctx.atom(render_sort(ty)));
                }
                smt_args.push(ctx.atom(render_sort(&out_type))); // output argument
                
                // (declare-fun ...)
                ctx.declare_fun(rel_name.clone(), smt_args, ctx.atom("Bool")).unwrap();
                
                // Functionality Axiom
                let func_ax = functionality_axiom(&rel_name, arg_types, &out_type);
                let func_ax_smt = expr_to_smt(&mut ctx, &func_ax).unwrap();
                ctx.assert(func_ax_smt).unwrap();
                
                // Injectivity Axiom
                let inj_ax = injectivity_axiom(&rel_name, arg_types, &out_type);
                let inj_ax_smt = expr_to_smt(&mut ctx, &inj_ax).unwrap();
                ctx.assert(inj_ax_smt).unwrap();
            }
            
            // Disjointness Axiom
            for i in 0..variants.len() {
                for j in (i + 1)..variants.len() {
                    let (cons1, args1) = &variants[i];
                    let (cons2, args2) = &variants[j];
                    let rel1 = sanitize_id(&format!("{}::{}_rel", enum_name, cons1));
                    let rel2 = sanitize_id(&format!("{}::{}_rel", enum_name, cons2));
                    let disj_ax = disjointness_axiom(&rel1, args1, &rel2, args2, &out_type);
                    let disj_ax_smt = expr_to_smt(&mut ctx, &disj_ax).unwrap();
                    ctx.assert(disj_ax_smt).unwrap();
                }
            }
        }

        // 3.3. 일반 함수 (Functions) 및 공리 선언
        for (func_name, def) in &program.functions {
            let (arg_types, out_type) = get_fun_types(&def.signature);
            let rel_name = format!("{}_rel", func_name);
            
            let mut smt_args = Vec::new();
            for ty in &arg_types {
                smt_args.push(ctx.atom(render_sort(ty)));
            }
            smt_args.push(ctx.atom(render_sort(&out_type)));
            
            ctx.declare_fun(rel_name.clone(), smt_args, ctx.atom("Bool")).unwrap();
            
            let func_ax = functionality_axiom(&rel_name, &arg_types, &out_type);
            let func_ax_smt = expr_to_smt(&mut ctx, &func_ax).unwrap();
            ctx.assert(func_ax_smt).unwrap();
        }

        // 3.4. 최종 검증 (Assert negated goal and check-sat)
        let goal_smt = expr_to_smt(&mut ctx, &relabs_expr).unwrap();
        println!("Goal SMT: {}", ctx.display(goal_smt));
        ctx.assert(goal_smt).unwrap();
        
        match ctx.check().unwrap() {
            easy_smt::Response::Sat => {
                return Err(format!(
                    "Failed to verify '{}': solver found counterexamples.\n## > 💾 Check the SMT query at: {}", 
                    goal_name, smt_log_path
                ));
            }
            easy_smt::Response::Unknown => {
                return Err(format!(
                    "Verification of '{}' cannot proceed: solver returned UNKNOWN.\n## > 💾 Check the SMT query at: {}", 
                    goal_name, smt_log_path
                ));
            }
            easy_smt::Response::Unsat => {
                // 성공: 테스트가 통과했으므로 쓸모없는 로그 파일을 삭제하여 폴더를 깔끔하게 유지합니다.
                let _ = fs::remove_file(&smt_log_path);
                println!("  ✅ [Verified] Solver returned UNSAT (Theorem {} is valid!)", goal_name);
            }
        }
    }
    
    Ok(())
}
