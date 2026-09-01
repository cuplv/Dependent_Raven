pub mod axioms;
pub mod builder;
pub mod solver;

use std::collections::HashMap;
use std::env;
use std::fs;

use crate::anf::{transform_expr as anf_transform, NameGenerator};
use crate::epr_check::{check_for_cycles, render_cycle};
use crate::nnf::transform_expr as nnf_transform;
use crate::relabs::transform_expr as relabs_transform;
use crate::smt::axioms::{disjointness_axiom, functionality_axiom, injectivity_axiom};
use crate::smt::builder::{expr_to_smt, render_sort, sanitize_id};
use crate::smt::solver::SolverConfig;
use frontend::ast::{BaseType, BinOp, Expr, Ident, Pattern, Program, Type, UnOp};
use frontend::typechecking::pattern_to_expr;

/// Extracts variables inside a pattern to create binders for the Forall quantifier.
/// This is used when creating axioms for pattern matching branches in recursive functions.
fn extract_pat_binders(pat: &Pattern, ty: &BaseType, binders: &mut Vec<(String, BaseType)>) {
    match pat {
        Pattern::Ident(name) => binders.push((name.clone(), ty.clone())),
        Pattern::Constructor { name, args, arg_types } => {
            // Field sorts come from arg_types, stamped by frontend::resolve::resolve_pattern_types.
            let field_types = arg_types.as_ref().unwrap_or_else(|| panic!(
                "Constructor pattern '{}' has unresolved field types (resolve_pattern_types was not run)",
                name
            ));
            for (arg, field_ty) in args.iter().zip(field_types.iter()) {
                extract_pat_binders(arg, field_ty, binders);
            }
        }
        Pattern::Wildcard => {}
        Pattern::Tuple(_) => {
            panic!("Tuple patterns are not yet supported in recursive function axiom generation")
        }
    }
}

/// [KOR] 함수의 시그니처에서 인자 타입 목록과 반환 타입을 추출합니다.
/// [ENG] Extracts the list of argument types and the return type from a function's signature.
pub(crate) fn get_fun_types(mut ty: &Type) -> (Vec<BaseType>, BaseType) {
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
    println!(
        "\n [Backend] Starting Pipeline for {} goals...",
        program.goals.len()
    );

    // 1. 디버깅 플래그 확인 (RAVENCHECK_DUMP_IR)
    let dump_ir = env::var("RAVENCHECK_DUMP_IR").is_ok();
    if dump_ir {
        let _ = fs::create_dir_all("logs");
    }

    struct ProcessedGoal {
        name: Ident,
        skolem_vars: Vec<(Ident, BaseType)>,
        relabs_expr: Expr,
        instantiations: Vec<Expr>,
    }

    let mut processed_goals = Vec::new();
    for goal in &program.goals {
        let negated_goal = Expr::UnOp {
            op: UnOp::Not,
            expr: Box::new(goal.property.clone()),
        };

        let mut gen = NameGenerator::new();
        let anf_expr = anf_transform(&negated_goal, &mut gen);
        let nnf_expr = nnf_transform(anf_expr.clone());

        // [KOR] Skolemize: 최상단 Exists 변수들을 뽑아내어 전역 상수(declare-const)로 만듭니다.
        let (skolem_vars, skolem_body) = crate::skolemize::skolemize_expr(&nnf_expr);

        let relabs_expr = relabs_transform(&skolem_body, &program.functions);

        let mut relabs_insts = Vec::new();
        for inst in &goal.instantiations {
            let inst_expr = Expr::Instantiate(Box::new(inst.clone()));
            let anf_inst = anf_transform(&inst_expr, &mut gen);
            let nnf_inst = nnf_transform(anf_inst);
            let relabs_inst = relabs_transform(&nnf_inst, &program.functions);
            relabs_insts.push(relabs_inst);
        }

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
        processed_goals.push(ProcessedGoal {
            name: goal.name.clone(),
            skolem_vars,
            relabs_expr,
            instantiations: relabs_insts,
        });
    }

    // 2. EPR 프래그먼트 검사 (Sort Cycle Check) - RelAbs 이후에 수행!
    let goals_for_check: Vec<_> = processed_goals
        .iter()
        .map(|g| g.relabs_expr.clone())
        .collect();
    if let Err(cycles) = check_for_cycles(&goals_for_check, &program.functions) {
        let mut err_msg = String::from("Found Sort Cycles! This breaks decidability.\n");
        for c in cycles {
            err_msg.push_str(&format!("   Cycle: {}\n", render_cycle(&c)));
        }
        return Err(err_msg);
    } else {
        println!(" [EPR Check Passed] No sort cycles detected. Logic is decidable.");
    }

    // 3. SMT 인코딩 및 실행
    let mut config = SolverConfig::default();

    // 로그 폴더가 없으면 미리 생성합니다.
    let _ = fs::create_dir_all("logs");

    for goal in processed_goals {
        let goal_name = goal.name;
        println!(" Solving Goal: {}", goal_name);

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
                if arg_types.is_empty() {
                    // [KOR] 인자가 없는 생성자 (예: Nat::Z)는 상수로 선언합니다.
                    let const_name = sanitize_id(&format!("{}::{}", enum_name, cons_name));
                    ctx.declare_const(const_name, ctx.atom(render_sort(&out_type)))
                        .unwrap();
                    // 상수는 Functionality와 Injectivity 공리가 필요 없습니다.
                } else {
                    // [KOR] 인자가 있는 생성자 (예: Nat::S)는 관계식으로 변환됨
                    let rel_name = sanitize_id(&format!("{}::{}_rel", enum_name, cons_name));

                    let mut smt_args = Vec::new();
                    for ty in arg_types {
                        smt_args.push(ctx.atom(render_sort(ty)));
                    }
                    smt_args.push(ctx.atom(render_sort(&out_type))); // output argument

                    // (declare-fun ...)
                    ctx.declare_fun(rel_name.clone(), smt_args, ctx.atom("Bool"))
                        .unwrap();

                    // Functionality Axiom
                    let func_ax = functionality_axiom(&rel_name, arg_types, &out_type);
                    let func_ax_smt = expr_to_smt(&mut ctx, &func_ax).unwrap();
                    ctx.assert(func_ax_smt).unwrap();

                    // Injectivity Axiom
                    let inj_ax = injectivity_axiom(&rel_name, arg_types, &out_type);
                    let inj_ax_smt = expr_to_smt(&mut ctx, &inj_ax).unwrap();
                    ctx.assert(inj_ax_smt).unwrap();
                }
            }

            // Disjointness Axiom
            for i in 0..variants.len() {
                for j in (i + 1)..variants.len() {
                    let (cons1, args1) = &variants[i];
                    let (cons2, args2) = &variants[j];

                    let disj_ax =
                        disjointness_axiom(enum_name, cons1, args1, cons2, args2, &out_type);
                    let disj_ax_smt = expr_to_smt(&mut ctx, &disj_ax).unwrap();
                    ctx.assert(disj_ax_smt).unwrap();
                }
            }
        }

        // 3.3. 일반 함수 (Functions) 및 공리 선언
        // [KOR] 두 단계로 나눕니다: 먼저 모든 함수의 관계를 선언하고, 그 다음에 정의
        //       공리를 assert합니다. 한 함수의 정의 공리는 다른 함수의 관계를 참조할 수
        //       있는데(예: count의 공리가 eq_nat_rel을 언급), `program.functions`는
        //       HashMap이라 순회 순서가 실행마다 달라서, 단일 루프에서는 아직 선언되지
        //       않은 관계를 참조하는 공리가 간헐적으로 solver 에러를 냈습니다.
        // [ENG] Two phases: declare ALL function relations first, THEN assert
        //       definitional axioms. A function's definitional axioms may reference
        //       other functions' relations (e.g. count's axioms mention eq_nat_rel),
        //       and `program.functions` is a HashMap with per-run iteration order --
        //       a single loop intermittently asserted axioms referencing relations
        //       that were not declared yet, killing the solver.
        for (func_name, def) in &program.functions {
            let (arg_types, out_type) = get_fun_types(&def.signature);
            let rel_name = format!("{}_rel", func_name);

            let mut smt_args = Vec::new();
            for ty in &arg_types {
                smt_args.push(ctx.atom(render_sort(ty)));
            }
            smt_args.push(ctx.atom(render_sort(&out_type)));

            ctx.declare_fun(rel_name.clone(), smt_args, ctx.atom("Bool"))
                .unwrap();

            let func_ax = functionality_axiom(&rel_name, &arg_types, &out_type);
            let func_ax_smt = expr_to_smt(&mut ctx, &func_ax).unwrap();
            ctx.assert(func_ax_smt).unwrap();
        }

        for (func_name, def) in &program.functions {
            let (_, out_type) = get_fun_types(&def.signature);

            // [KOR] 본문이 있는 모든 "값 반환" 함수(재귀든 아니든)의 본문을 분해하여
            //       브랜치별 정의 공리를 생성합니다. 비재귀 함수는 자기 호출이 0개인
            //       재귀 함수일 뿐이며, 아래 leaf 케이스가 `forall params. f(params) == body`를
            //       그대로 만들어냅니다. (G3)
            //       Unit 반환 함수는 제외합니다: Lemma의 본문은 정의가 아니라 증명
            //       스크립트이므로, `tip_x(..) == ()` 같은 공리는 무의미하고 그 Tuple
            //       leaf는 expr_to_smt에서 panic합니다.
            // [ENG] Emit per-branch definitional axioms for EVERY bodied, value-returning
            //       function (recursive or not) -- a non-recursive function is just a
            //       recursive function with zero self-calls; the leaf case below emits
            //       `forall params. f(params) == body` as-is. (G3)
            //       Unit-returning functions are excluded: lemma bodies are proof
            //       scripts, not definitions -- a `tip_x(..) == ()` axiom would be
            //       meaningless and its Tuple leaf panics in expr_to_smt.
            if out_type != BaseType::Unit {
                if let Some(body_expr) = &def.body {
                    // Extract the names and base types of all formal parameters of the function.
                    let mut params = Vec::new();
                    let mut curr_ty = &def.signature;
                    while let Type::Arrow(f) = curr_ty {
                        let base_ty = match &*f.param_type {
                            Type::Base(b)
                            | Type::Refined(frontend::ast::RefinedType { base: b, .. }) => {
                                b.clone()
                            }
                            _ => panic!("Complex param types not supported in backend"),
                        };
                        params.push((f.param_name.clone(), base_ty));
                        curr_ty = &*f.ret_type;
                    }

                    // Initialize the arguments map with the identity mapping (x -> Var(x))
                    let mut initial_args_map = HashMap::new();
                    let mut initial_binders = Vec::new();
                    for (p_name, p_ty) in &params {
                        initial_args_map.insert(p_name.clone(), Expr::Var(p_name.clone()));
                        initial_binders.push((p_name.clone(), p_ty.clone()));
                    }

                    // Recursively flatten nested matches/ifs and generate axioms
                    generate_axioms_from_body(
                        body_expr,
                        &initial_args_map,
                        &initial_binders,
                        &func_name,
                        &params,
                        &[],
                        &mut ctx,
                        &program,
                    );
                }
            }
        }

        // 3.4. Skolem Variables 및 Instantiations 추가
        // [KOR] Phase 2에서 뽑아낸 전역 상수(Skolem variables)들을 선언합니다.
        for (var_name, var_type) in &goal.skolem_vars {
            ctx.declare_const(sanitize_id(var_name), ctx.atom(render_sort(var_type)))
                .unwrap();
        }

        // [KOR] Phase 3에서 변환한 인스턴스화 공리들을 각각 별도의 assert(exists ...) 구문으로 꽂아 넣습니다.
        for inst_expr in &goal.instantiations {
            let inst_smt = expr_to_smt(&mut ctx, inst_expr).unwrap();
            ctx.assert(inst_smt).unwrap();
        }

        // 3.5. 최종 검증 (Assert negated goal and check-sat)
        let goal_smt = expr_to_smt(&mut ctx, &goal.relabs_expr).unwrap();
        // println!("Goal SMT: {}", ctx.display(goal_smt)); // 너무 길면 주석 처리
        ctx.assert(goal_smt).unwrap();

        match ctx.check().unwrap() {
            easy_smt::Response::Sat => {
                // [KOR] 반례 파일을 소스 어휘로 방출합니다. 방출 실패가 검증 실패
                //       보고 자체를 가리면 안 되므로, 에러는 경고로만 출력합니다.
                // [ENG] Emit the counterexample file in source vocabulary. Emission
                //       failure must never mask the verification failure itself,
                //       so its error is only printed as a warning.
                let cex_path = format!("logs/{}_counterexample.smt2", goal_name);
                if let Some(src_goal) = program.goals.iter().find(|g| g.name == goal_name) {
                    // [KOR] 방출기 내부의 불변식 panic도 경고로 낮춥니다.
                    // [ENG] Invariant panics inside the emitter are also
                    //       downgraded to warnings.
                    let emitted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        crate::cex::emit(&program, src_goal, &cex_path)
                    }));
                    match emitted {
                        Ok(Ok(())) => {}
                        Ok(Err(e)) => {
                            println!("  ⚠️ Failed to write counterexample {}: {}", cex_path, e)
                        }
                        Err(_) => println!(
                            "  ⚠️ Counterexample generation panicked; {} was not written",
                            cex_path
                        ),
                    }
                }
                return Err(format!(
                    "Failed to verify '{}': solver found counterexamples.\n## > 💾 Check the SMT query at: {}\n## > 💾 Counterexample: {}",
                    goal_name, smt_log_path, cex_path
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
                println!(
                    "  ✅ [Verified] Solver returned UNSAT (Theorem {} is valid!)",
                    goal_name
                );
            }
        }
    }

    Ok(())
}

/// Recursively traverses a function body to flatten nested `Match` expressions.
/// When a leaf expression (no top-level `Match`) is reached, it constructs an equality axiom
/// and passes it through the standard transformation pipeline (ANF -> NNF -> RelAbs) to be asserted in the SMT context.
fn generate_axioms_from_body(
    expr: &Expr,
    args_map: &HashMap<Ident, Expr>,
    binders: &Vec<(Ident, BaseType)>,
    func_name: &str,
    params: &[(Ident, BaseType)],
    guards: &[Expr],
    ctx: &mut easy_smt::Context,
    program: &Program,
) {
    if let Expr::Match {
        expr: match_target,
        arms,
    } = expr
    {
        // We assume the match target is a simple variable in this backend axiom generation phase.
        let matched_var = match &**match_target {
            Expr::Var(v) => v.clone(),
            _ => panic!("Match target must be a simple variable for backend axiom generation"),
        };

        for (pat, arm_expr) in arms {
            let mut new_args_map = args_map.clone();
            let mut new_binders = binders.clone();

            // Convert the pattern to an expression (e.g., `Constructor("Nat::S", [Var("x_min")])`)
            let pat_expr = pattern_to_expr(pat);

            // Determine the base type of the matched variable to correctly type the new binders
            // In a fully generalized system, we would look up the specific constructor's signature,
            // but for simplicity, we assume recursive arguments have the same type as the parent.
            let matched_ty = binders
                .iter()
                .find(|(n, _)| n == &matched_var)
                .unwrap()
                .1
                .clone();

            // Extract any new variables introduced inside the pattern and add them to the universal binders
            extract_pat_binders(pat, &matched_ty, &mut new_binders);

            // Remove the original matched variable from the binders, as it is now instantiated
            new_binders.retain(|(n, _)| n != &matched_var);

            // Update the arguments map: substitute the matched variable with the pattern expression.
            // The substitution must also reach the EXISTING map values: when the matched
            // variable was itself bound by an enclosing pattern (e.g. matching on `t` after
            // `xs` matched `Cons(h, t)`), the accumulated entry `xs -> Cons(h, t)` still
            // mentions it, and leaving it unsubstituted would emit an axiom with a free `t`.
            for val in new_args_map.values_mut() {
                *val = frontend::env::substitute_expr(val, &matched_var, &pat_expr);
            }
            new_args_map.insert(matched_var.clone(), pat_expr.clone());

            // CRUCIAL: Substitute occurrences of the matched variable with the pattern expression
            // inside the arm's body. If the body uses `x` and `x` was matched against `Nat::S(x_min)`,
            // `x` in the body must be replaced by `Nat::S(x_min)` so no unbound variables remain.
            let substituted_body =
                frontend::env::substitute_expr(arm_expr, &matched_var, &pat_expr);

            // Guards accumulated from enclosing `if`s may also mention the matched
            // variable; substitute so they stay consistent with the instantiated
            // pattern (otherwise the final axiom would contain an unbound variable).
            let substituted_guards: Vec<Expr> = guards
                .iter()
                .map(|g| frontend::env::substitute_expr(g, &matched_var, &pat_expr))
                .collect();

            // Recursively process the substituted body of this arm
            generate_axioms_from_body(
                &substituted_body,
                &new_args_map,
                &new_binders,
                func_name,
                params,
                &substituted_guards,
                ctx,
                program,
            );
        }
    } else if let Expr::If { cond, then_expr, else_expr } = expr {
        // Branch conditions become guards on the branch's equations (G3):
        //   then-branch:  guards, cond      |-  f(args) == then_expr
        //   else-branch:  guards, not cond  |-  f(args) == else_expr
        // Each branch yields its own single-polarity axiom, which the standard
        // ANF -> NNF -> RelAbs pipeline encodes like any other formula (calls
        // inside `cond` get relationally abstracted along the way).
        let mut then_guards = guards.to_vec();
        then_guards.push((**cond).clone());
        generate_axioms_from_body(
            then_expr, args_map, binders, func_name, params, &then_guards, ctx, program,
        );

        let mut else_guards = guards.to_vec();
        else_guards.push(Expr::UnOp {
            op: UnOp::Not,
            expr: cond.clone(),
        });
        generate_axioms_from_body(
            else_expr, args_map, binders, func_name, params, &else_guards, ctx, program,
        );
    } else {
        // We have reached a leaf expression (no top-level `Match`).
        // Construct the Left-Hand Side (LHS) of the equation using the original parameter order
        // and the accumulated instantiations in `args_map`.
        let mut lhs_args = Vec::new();
        for (p_name, _) in params {
            lhs_args.push(args_map.get(p_name).unwrap().clone());
        }

        let lhs = Expr::Call {
            func: func_name.to_string(),
            args: lhs_args,
        };

        // Form the equation: LHS == RHS (where RHS is the leaf expression)
        let eq_expr = Expr::BinOp {
            op: BinOp::Eq,
            left: Box::new(lhs),
            right: Box::new(expr.clone()),
        };

        // Guards from enclosing `if` branches condition the equation:
        // (g1 && ... && gn) => f(args) == leaf. Under the partial-function
        // semantics, an instance whose guard terms are undefined is vacuously
        // satisfied, so this introduces no new incompleteness class beyond the
        // usual "instantiate the terms you need".
        let axiom_body = match guards.iter().cloned().reduce(|acc, g| Expr::BinOp {
            op: BinOp::And,
            left: Box::new(acc),
            right: Box::new(g),
        }) {
            Some(guard_conj) => Expr::BinOp {
                op: BinOp::Implies,
                left: Box::new(guard_conj),
                right: Box::new(eq_expr),
            },
            None => eq_expr,
        };

        // Wrap the equation in a Forall quantifier over all accumulated active binders.
        let axiom = if binders.is_empty() {
            axiom_body
        } else {
            Expr::Forall {
                binders: binders.clone(),
                body: Box::new(axiom_body),
            }
        };

        // Pass this raw axiom through the standard transformation pipeline
        // (ANF -> NNF -> RelAbs) just like the main verification goal.
        // This flattens nested calls into `Let` bindings, pushes negations, and finally
        // transforms them into relational logic (Implies), entirely avoiding sort cycles.
        let mut gen = NameGenerator::new();
        let anf_expr = anf_transform(&axiom, &mut gen);
        let nnf_expr = nnf_transform(anf_expr);
        let relabs_expr = relabs_transform(&nnf_expr, &program.functions);

        // Convert the fully processed relation expression to SMT-LIB2 format and assert it.
        let smt_expr = expr_to_smt(ctx, &relabs_expr).unwrap();
        ctx.assert(smt_expr).unwrap();
    }
}
