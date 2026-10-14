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
use crate::smt::axioms::{
    disjointness_axiom, functionality_axiom, injectivity_axiom, subterm_irreflexivity_axiom,
    subterm_step_axiom, subterm_transitivity_axiom,
};
use crate::smt::builder::{expr_to_smt, render_sort, sanitize_id};
use crate::smt::solver::{Query, Verdict};
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

/// True iff some `match` in `expr` scrutinises the variable `name`.
pub(crate) fn is_match_scrutinee(name: &Ident, expr: &Expr) -> bool {
    match expr {
        Expr::Match { expr: target, arms } => {
            matches!(&**target, Expr::Var(v) if v == name)
                || arms.iter().any(|(_, arm)| is_match_scrutinee(name, arm))
        }
        Expr::If { cond, then_expr, else_expr } => {
            is_match_scrutinee(name, cond)
                || is_match_scrutinee(name, then_expr)
                || is_match_scrutinee(name, else_expr)
        }
        Expr::Let { bound_expr, body, .. } => {
            is_match_scrutinee(name, bound_expr) || is_match_scrutinee(name, body)
        }
        _ => false,
    }
}

/// Base sort of a let-bound expression in a function body, for its quantifier
/// binder. Calls take their declared return sort, constructors their datatype,
/// variables the sort they were bound with; logical operators are Bool.
fn infer_let_sort(
    expr: &Expr,
    binders: &[(Ident, BaseType)],
    program: &Program,
    func_name: &str,
) -> BaseType {
    match expr {
        Expr::Var(v) => binders
            .iter()
            .find(|(n, _)| n == v)
            .map(|(_, t)| t.clone())
            .unwrap_or_else(|| panic!("unbound variable `{}` in the body of `{}`", v, func_name)),
        Expr::Call { func, .. } => program
            .functions
            .get(func)
            .map(|def| get_fun_types(&def.signature).1)
            .unwrap_or_else(|| panic!("unknown function `{}` in the body of `{}`", func, func_name)),
        Expr::Constructor { name, .. } => match name.rsplit_once("::") {
            Some((enum_name, _)) => BaseType::Custom(enum_name.to_string()),
            None => panic!("constructor `{}` is not qualified as 'Enum::Variant'", name),
        },
        Expr::BoolConst(_) | Expr::BinOp { .. } | Expr::UnOp { .. } => BaseType::Bool,
        Expr::If { then_expr, .. } => infer_let_sort(then_expr, binders, program, func_name),
        other => panic!(
            "cannot determine the sort of let-bound expression {:?} in the body of `{}`",
            other, func_name
        ),
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
    // 로그 폴더가 없으면 미리 생성합니다.
    let _ = fs::create_dir_all("logs");

    // [KOR] 실패한 goal마다 보고 한 건. 첫 실패에서 멈추지 않고 모든 goal을 풉니다.
    // [ENG] One report per failing goal. Every goal is solved; the run does not
    //       stop at the first failure.
    let mut failures: Vec<String> = Vec::new();

    // [ENG] The frontier engine's switches and, when it is on, the structured
    //       equations it unfolds against (the same record the axioms are rendered from).
    let frontier_cfg = crate::frontier::Config::from_env();
    let equations = if frontier_cfg.enabled { definitional_equations(&program) } else { Vec::new() };

    for mut goal in processed_goals {
        let goal_name = goal.name.clone();
        println!(" Solving Goal: {}", goal_name);

        // [KOR] 질의는 항상 이 .smt2 파일에 쓰이고, 솔버는 그 파일에 대해 실행됩니다.
        // [ENG] The query is always written to this .smt2 file; the solver runs on it.
        let smt_log_path = format!("logs/{}_failed_query.smt2", goal_name);

        // [KOR] 질의 조립(소트·생성자·공리·skolem 상수·증인·부정된 goal)은 `build_query`
        //       (§6.1 1–10단계)로 옮겨졌고, 아래 루프가 라운드마다 다시 부릅니다.
        //       기호적 경계 루프(RAVENCHECK_AUTO_INST, `doc/auto_instantiation_plan.md`
        //       §5): 풀고, 증명되지 않으면 장부를 한 단계 전개해 빠진 적용 항을 힌트로
        //       더한 뒤 다시 풉니다. 포화(라운드가 아무것도 더하지 못함)나 깊이 한도에서
        //       멈춥니다. 꺼져 있으면 한 번 풀고 끝납니다.
        // [ENG] Query assembly (sorts, constructors, axioms, skolem constants,
        //       witnesses, negated goal) lives in `build_query` (§6.1 steps 1–10);
        //       the loop below calls it once per round. The symbolic-frontier loop
        //       (RAVENCHECK_AUTO_INST, `doc/auto_instantiation_plan.md` §5): solve;
        //       if not proved, unfold the ledger one step, add the missing
        //       applications as hints, solve again. Stops at saturation (a round
        //       adds nothing) or at the depth cap. Off, it is a single solve.
        let mut source_goal = program.goals.iter().find(|g| g.name == goal_name).cloned();
        let mut shapes = crate::frontier::shape::Shapes::default();
        let mut rounds: Vec<Vec<Expr>> = Vec::new();
        let mut stop: Option<crate::frontier::Stop> = None;
        let (verdict, model) = loop {
            let ctx = build_query(&program, &goal);
            let (verdict, model) = ctx.solve(&smt_log_path);
            if verdict == Verdict::Unsat || !frontier_cfg.enabled {
                break (verdict, model);
            }
            let Some(src) = source_goal.as_mut() else {
                break (verdict, model);
            };
            if rounds.len() >= frontier_cfg.depth {
                stop = Some(crate::frontier::Stop::Limited { depth: frontier_cfg.depth });
                break (verdict, model);
            }
            let round = crate::frontier::candidates::round(&equations, src, &mut shapes);
            if frontier_cfg.suggest {
                println!("{}", crate::frontier::suggestion(&round));
                break (verdict, model);
            }
            if round.added.is_empty() {
                stop = Some(crate::frontier::Stop::Saturated { stuck: round.stuck });
                break (verdict, model);
            }
            for cand in &round.added {
                src.instantiations.push(cand.clone());
                goal.instantiations.push(relabs_hint(&program, cand));
            }
            rounds.push(round.added);
        };
        if verdict != Verdict::Unsat {
            // [KOR] 반례 파일을 소스 어휘로 방출합니다. 파일은 goal과 그 인스턴스화
            //       목록(ledger)에서 만들어지며 solver 모델을 읽지 않으므로, 답이
            //       UNKNOWN(시간 초과)이어도 쓸 수 있습니다. 방출 실패가 검증 실패
            //       보고 자체를 가리면 안 되므로, 에러는 경고로만 출력합니다.
            // [ENG] Emit the counterexample file in source vocabulary. It is built
            //       from the goal and its instantiation list (the ledger), never
            //       from a solver model, so it is written for an UNKNOWN (timed
            //       out) goal as well. Emission failure must never mask the
            //       verification failure itself, so its error is only printed as
            //       a warning.
            let cex_path = format!("logs/{}_instantiated_terms.smt2", goal_name);
            let mut cex_written = false;
            if let Some(src_goal) = program.goals.iter().find(|g| g.name == goal_name) {
                let label = if verdict == Verdict::Sat { "sat" } else { "unknown" };
                // [KOR] 방출기 내부의 불변식 panic도 경고로 낮춥니다.
                // [ENG] Invariant panics inside the emitter are also
                //       downgraded to warnings.
                let emitted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    crate::cex::emit(&program, src_goal, label, &cex_path)
                }));
                match emitted {
                    Ok(Ok(())) => cex_written = true,
                    Ok(Err(e)) => {
                        println!("  ⚠️ Failed to write instantiated terms {}: {}", cex_path, e)
                    }
                    Err(_) => println!(
                        "  ⚠️ Instantiated-terms emission panicked; {} was not written",
                        cex_path
                    ),
                }
            }
            // Only advertise the instantiated-terms file if it was actually written.
            let mut cex_line = if cex_written {
                format!("\n## > 💾 Instantiated terms: {}", cex_path)
            } else {
                String::new()
            };
            // [KOR] 반례 모델: `sat`을 낸 바로 그 z3 실행의 유한 모델을 CamlStar의 JSON
            //       형식으로 파일에 쓰고 출력합니다.
            // [ENG] The countermodel: the finite model of the very z3 run that
            //       answered `sat`, written and printed in CamlStar's JSON form.
            if let Some(model) = &model {
                let json = crate::model::print::camlstar_json(model, &program, &goal.skolem_vars);
                let model_path = format!("logs/{}_model.json", goal_name);
                match fs::write(&model_path, format!("{}\n", json)) {
                    Ok(()) => cex_line.push_str(&format!("\n## > 💾 Model: {}", model_path)),
                    Err(e) => println!("  ⚠️ Failed to write model {}: {}", model_path, e),
                }
                println!("{}", json);
            }
            // [ENG] What the frontier did before giving up, if it ran (trace only).
            if let (true, Some(stop)) = (frontier_cfg.trace, &stop) {
                cex_line.push_str(&crate::frontier::stop_report(stop, &rounds));
            }
            failures.push(if verdict == Verdict::Sat {
                format!(
                    "Failed to verify '{}': solver found counterexamples.\n## > 💾 Check the SMT query at: {}{}",
                    goal_name, smt_log_path, cex_line
                )
            } else {
                format!(
                    "Verification of '{}' cannot proceed: solver returned UNKNOWN.\n## > 💾 Check the SMT query at: {}{}",
                    goal_name, smt_log_path, cex_line
                )
            });
        }
        if verdict == Verdict::Unsat {
            // 성공: 테스트가 통과했으므로 쓸모없는 로그 파일을 삭제하여 폴더를 깔끔하게 유지합니다.
            // Set RAVENCHECK_KEEP_QUERIES to keep the query of a verified goal
            // (to inspect a passing VC's query, or to measure query sizes and
            // solver times). The file keeps its replay-file name.
            if std::env::var("RAVENCHECK_KEEP_QUERIES").is_err() {
                let _ = fs::remove_file(&smt_log_path);
            }
            println!(
                "  ✅ [Verified] Solver returned UNSAT (Theorem {} is valid!)",
                goal_name
            );
            if frontier_cfg.trace && !rounds.is_empty() {
                print!("{}", crate::frontier::verified_report(&rounds, source_goal.as_ref()));
            }
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n##\n## > "))
    }
}

/// [ENG] A goal after phase A: negated, ANF'd, NNF'd, skolemized, relationally
///       abstracted; its hints likewise. The frontier loop appends to
///       `instantiations` between rounds.
struct ProcessedGoal {
    name: Ident,
    skolem_vars: Vec<(Ident, BaseType)>,
    relabs_expr: Expr,
    instantiations: Vec<Expr>,
}

/// [KOR] 힌트 하나를 goal의 힌트와 같은 경로로 변환합니다: Instantiate → ANF → NNF →
///       RelAbs. 경계 루프가 라운드 사이에 더하는 후보에 씁니다.
/// [ENG] One hint through the same path as the goal's own hints:
///       Instantiate → ANF → NNF → RelAbs. Used by the frontier loop for the
///       candidates it adds between rounds (fresh ANF names are fine: each hint is
///       its own `(assert (exists ...))`).
fn relabs_hint(program: &Program, hint: &Expr) -> Expr {
    let inst_expr = Expr::Instantiate(Box::new(hint.clone()));
    let mut gen = NameGenerator::new();
    let anf_inst = anf_transform(&inst_expr, &mut gen);
    let nnf_inst = nnf_transform(anf_inst);
    relabs_transform(&nnf_inst, &program.functions)
}

/// [KOR] 한 goal의 질의를 처음부터 조립합니다 (§6.1의 1–10단계): 소트, 생성자와 구조
///       공리, 함수 관계와 functionality, 정의 공리, skolem 상수, 인스턴스화 증인,
///       부정된 goal. 경계 루프는 라운드마다 이 함수를 다시 부릅니다.
/// [ENG] Assembles one goal's query from scratch (steps 1–10 of §6.1): sorts,
///       constructors with their structural axioms, function relations with
///       functionality, definitional axioms, skolem constants, instantiation
///       witnesses, the negated goal. The frontier loop calls it once per round.
fn build_query(program: &Program, goal: &ProcessedGoal) -> Query {
    let mut ctx = Query::new();

    // [KOR] Unit 소트 선언 (프론트엔드에서 넘어올 수 있으므로)
    ctx.declare_sort("Unit".to_string());
    let unit_sort = ctx.smt.atom("Unit");
    ctx.declare_const("unit_val".to_string(), unit_sort);

    // 3.1. 소트(Sort) 선언
    for (enum_name, _) in &program.datatypes {
        let sort_name = render_sort(&BaseType::Custom(enum_name.clone()));
        ctx.declare_sort(sort_name);
    }

    // 3.2. 데이터 생성자 (Constructors) 및 공리 선언
    for (enum_name, variants) in &program.datatypes {
        let out_type = BaseType::Custom(enum_name.clone());

        // [KOR] 부분항 순서(subterm) 관계: 재귀 필드(자기 sort의 필드)를 가진 datatype에만 선언합니다.
        // [ENG] Subterm order relation, declared only for datatypes with a recursive field.
        let has_recursive_field = variants
            .iter()
            .any(|(_, args)| args.iter().any(|ty| *ty == out_type));
        let sub_rel = sanitize_id(&format!("{}::subterm", enum_name));
        if has_recursive_field {
            let sub_args = vec![ctx.atom(render_sort(&out_type)), ctx.atom(render_sort(&out_type))];
            ctx.declare_fun(sub_rel.clone(), sub_args, ctx.atom("Bool"));
        }

        for (cons_name, arg_types) in variants {
            if arg_types.is_empty() {
                // [KOR] 인자가 없는 생성자 (예: Nat::Z)는 상수로 선언합니다.
                let const_name = sanitize_id(&format!("{}::{}", enum_name, cons_name));
                ctx.declare_const(const_name, ctx.atom(render_sort(&out_type)));
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
                ctx.declare_fun(rel_name.clone(), smt_args, ctx.atom("Bool"));

                // Functionality Axiom
                let func_ax = functionality_axiom(&rel_name, arg_types, &out_type);
                let func_ax_smt = expr_to_smt(&mut ctx.smt, &func_ax).unwrap();
                ctx.assert(func_ax_smt);

                // Injectivity Axiom
                let inj_ax = injectivity_axiom(&rel_name, arg_types, &out_type);
                let inj_ax_smt = expr_to_smt(&mut ctx.smt, &inj_ax).unwrap();
                ctx.assert(inj_ax_smt);

                // Subterm Step Axiom: each recursive field is a proper subterm of the result.
                for (i, ty) in arg_types.iter().enumerate() {
                    if *ty == out_type {
                        let step_ax =
                            subterm_step_axiom(&rel_name, arg_types, i, &sub_rel, &out_type);
                        let step_ax_smt = expr_to_smt(&mut ctx.smt, &step_ax).unwrap();
                        ctx.assert(step_ax_smt);
                    }
                }
            }
        }

        // Disjointness Axiom
        for i in 0..variants.len() {
            for j in (i + 1)..variants.len() {
                let (cons1, args1) = &variants[i];
                let (cons2, args2) = &variants[j];

                let disj_ax =
                    disjointness_axiom(enum_name, cons1, args1, cons2, args2, &out_type);
                let disj_ax_smt = expr_to_smt(&mut ctx.smt, &disj_ax).unwrap();
                ctx.assert(disj_ax_smt);
            }
        }

        // Subterm order: transitive and irreflexive. With the step facts this
        // excludes every finite constructor cycle (acyclicity), using only
        // universal quantifiers, so the EPR fragment is preserved.
        if has_recursive_field {
            for ax in [
                subterm_transitivity_axiom(&sub_rel, &out_type),
                subterm_irreflexivity_axiom(&sub_rel, &out_type),
            ] {
                let ax_smt = expr_to_smt(&mut ctx.smt, &ax).unwrap();
                ctx.assert(ax_smt);
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

        ctx.declare_fun(rel_name.clone(), smt_args, ctx.atom("Bool"));

        let func_ax = functionality_axiom(&rel_name, &arg_types, &out_type);
        let func_ax_smt = expr_to_smt(&mut ctx.smt, &func_ax).unwrap();
        ctx.assert(func_ax_smt);
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
            for eq in equations_of(func_name, def, program) {
                assert_equation(&mut ctx, program, &eq);
            }
        }
    }

    // 3.4. Skolem Variables 및 Instantiations 추가
    // [KOR] Phase 2에서 뽑아낸 전역 상수(Skolem variables)들을 선언합니다.
    for (var_name, var_type) in &goal.skolem_vars {
        ctx.declare_const(sanitize_id(var_name), ctx.atom(render_sort(var_type)));
    }

    // [KOR] Phase 3에서 변환한 인스턴스화 공리들을 각각 별도의 assert(exists ...) 구문으로 꽂아 넣습니다.
    for inst_expr in &goal.instantiations {
        let inst_smt = expr_to_smt(&mut ctx.smt, inst_expr).unwrap();
        ctx.assert(inst_smt);
    }

    // 3.5. 최종 검증 (Assert negated goal and check-sat)
    let goal_smt = expr_to_smt(&mut ctx.smt, &goal.relabs_expr).unwrap();
    ctx.assert(goal_smt);

    ctx
}

/// [KOR] 함수의 가드된 정의 등식 하나: match/if 트리의 잎 하나. `args`는 둘러싼
///       `match`들의 패턴을 대입한 매개변수(등식의 인자 패턴), `guards`는 잎까지의
///       경로에 있는 `if` 조건(과 let-scrutinee 등식), `rhs`는 잎입니다.
///       `assert_equation`이 solver용으로 렌더링하고, 경계(frontier) 엔진이 기호적으로
///       매칭합니다 — "한 단계 전개"의 개념은 이 하나뿐입니다.
/// [ENG] One guarded defining equation of a function: one leaf of its match/if
///       tree. `args` are the parameters with the enclosing `match` patterns
///       substituted (the equation's argument patterns), `guards` the `if`
///       conditions (and let-scrutinee equalities) on the path to the leaf,
///       `rhs` the leaf. `assert_equation` renders it for the solver; the
///       frontier engine matches it symbolically — one notion of "unfold one
///       step".
#[derive(Debug, Clone)]
pub struct DefEq {
    pub func: Ident,
    pub binders: Vec<(Ident, BaseType)>,
    pub args: Vec<Expr>,
    pub guards: Vec<Expr>,
    pub rhs: Expr,
}

/// [ENG] The structured definitional equations of every bodied, value-returning
///       function (lemmas, which return Unit, have none), in `program.functions`
///       order.
pub fn definitional_equations(program: &Program) -> Vec<DefEq> {
    let mut out = Vec::new();
    for (func_name, def) in &program.functions {
        out.extend(equations_of(func_name, def, program));
    }
    out
}

/// [ENG] The equations of one function; empty for a Unit-returning or bodiless one.
fn equations_of(func_name: &str, def: &frontend::ast::FunctionDef, program: &Program) -> Vec<DefEq> {
    let (_, out_type) = get_fun_types(&def.signature);
    if out_type == BaseType::Unit {
        return Vec::new();
    }
    let Some(body_expr) = &def.body else {
        return Vec::new();
    };

    // Extract the names and base types of all formal parameters of the function.
    let mut params = Vec::new();
    let mut curr_ty = &def.signature;
    while let Type::Arrow(f) = curr_ty {
        let base_ty = match &*f.param_type {
            Type::Base(b) | Type::Refined(frontend::ast::RefinedType { base: b, .. }) => b.clone(),
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

    let mut out = Vec::new();
    collect_equations(
        body_expr,
        &initial_args_map,
        &initial_binders,
        func_name,
        &params,
        &[],
        program,
        &mut out,
    );
    out
}

/// [ENG] Assert one equation as `forall binders. (g1 && ... && gn) => f(args) == rhs`,
///       passed through ANF -> NNF -> RelAbs like the main goal.
fn assert_equation(ctx: &mut Query, program: &Program, eq: &DefEq) {
    let lhs = Expr::Call {
        func: eq.func.clone(),
        args: eq.args.clone(),
    };

    // Form the equation: LHS == RHS (where RHS is the leaf expression)
    let eq_expr = Expr::BinOp {
        op: BinOp::Eq,
        left: Box::new(lhs),
        right: Box::new(eq.rhs.clone()),
    };

    // Guards from enclosing `if` branches condition the equation:
    // (g1 && ... && gn) => f(args) == leaf. Under the partial-function
    // semantics, an instance whose guard terms are undefined is vacuously
    // satisfied, so this introduces no new incompleteness class beyond the
    // usual "instantiate the terms you need".
    let axiom_body = match eq.guards.iter().cloned().reduce(|acc, g| Expr::BinOp {
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
    let axiom = if eq.binders.is_empty() {
        axiom_body
    } else {
        Expr::Forall {
            binders: eq.binders.clone(),
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
    let smt_expr = expr_to_smt(&mut ctx.smt, &relabs_expr).unwrap();
    ctx.assert(smt_expr);
}

/// Recursively traverses a function body to flatten nested `Match`/`If`/`Let`
/// expressions. Each leaf (no top-level `Match`) becomes one `DefEq` in `out`.
fn collect_equations(
    expr: &Expr,
    args_map: &HashMap<Ident, Expr>,
    binders: &Vec<(Ident, BaseType)>,
    func_name: &str,
    params: &[(Ident, BaseType)],
    guards: &[Expr],
    program: &Program,
    out: &mut Vec<DefEq>,
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
            collect_equations(
                &substituted_body,
                &new_args_map,
                &new_binders,
                func_name,
                params,
                &substituted_guards,
                program,
                out,
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
        collect_equations(
            then_expr, args_map, binders, func_name, params, &then_guards, program, out,
        );

        let mut else_guards = guards.to_vec();
        else_guards.push(Expr::UnOp {
            op: UnOp::Not,
            expr: cond.clone(),
        });
        collect_equations(
            else_expr, args_map, binders, func_name, params, &else_guards, program, out,
        );
    } else if let Expr::Let { pat, bound_expr, body } = expr {
        // The leaf pipeline cannot split an `if`/`match` hidden under a `let`,
        // so every `let` is peeled here, in one of two ways:
        //  - `x` is a match scrutinee in `body`: keep `x` as a universally
        //    quantified binder and add the guard `x == e` (as T-LET does in
        //    proofs). The Match case then substitutes `x := C(..)` into that
        //    guard, giving the path condition `C(..) == e`.
        //  - otherwise: substitute `e` for `x` (shadow-aware). A guard `x == e`
        //    would demand a definedness witness for `e` in EVERY branch, even
        //    ones that never use `x`; substitution only asks for it where used.
        match pat {
            Pattern::Ident(name) if !is_match_scrutinee(name, body) => {
                let substituted = frontend::env::substitute_expr(body, name, bound_expr);
                collect_equations(
                    &substituted, args_map, binders, func_name, params, guards, program, out,
                );
            }
            Pattern::Ident(name) => {
                if binders.iter().any(|(n, _)| n == name) {
                    panic!(
                        "let-binding `{}` in the body of `{}` shadows a variable in scope; rename it",
                        name, func_name
                    );
                }
                let sort = infer_let_sort(bound_expr, binders, program, func_name);
                let mut new_binders = binders.clone();
                new_binders.push((name.clone(), sort));
                let mut new_guards = guards.to_vec();
                new_guards.push(Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(Expr::Var(name.clone())),
                    right: bound_expr.clone(),
                });
                collect_equations(
                    body, args_map, &new_binders, func_name, params, &new_guards, program, out,
                );
            }
            // `let _ = e;` binds nothing in a function body.
            Pattern::Wildcard => collect_equations(
                body, args_map, binders, func_name, params, guards, program, out,
            ),
            other => panic!(
                "unsupported let pattern {:?} in the body of `{}`",
                other, func_name
            ),
        }
    } else {
        // We have reached a leaf expression (no top-level `Match`): one equation.
        // Its argument patterns are the parameters in their original order with
        // the accumulated pattern substitutions of `args_map` applied.
        let mut args = Vec::new();
        for (p_name, _) in params {
            args.push(args_map.get(p_name).unwrap().clone());
        }
        out.push(DefEq {
            func: func_name.to_string(),
            binders: binders.clone(),
            args,
            guards: guards.to_vec(),
            rhs: expr.clone(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // [ENG] A self-registered program (no names from the test suite): one datatype,
    //       a recursive function, a function with a nested match and an `if`.
    fn program() -> Program {
        let mut program = Program { datatypes: HashMap::new(), functions: HashMap::new(), goals: Vec::new() };
        frontend::api::register_enum(&mut program, "Peano", "enum Peano { Zero, Succ(Box<Peano>) }");
        frontend::api::register_val(
            &mut program,
            "flag",
            None,
            "fn flag(x: Peano) -> bool { match x { Peano::Zero => true, Peano::Succ(_x1) => false } }",
            false,
        );
        frontend::api::register_val(
            &mut program,
            "plus",
            None,
            "fn plus(x: Peano, y: Peano) -> Peano { match x { Peano::Zero => y, Peano::Succ(x1) => Peano::Succ(Box::new(plus(*x1, y))) } }",
            true,
        );
        frontend::api::register_val(
            &mut program,
            "pick",
            None,
            "fn pick(x: Peano, y: Peano) -> Peano { match x { Peano::Zero => y, Peano::Succ(x1) => match y { Peano::Zero => x, Peano::Succ(y1) => if flag(*x1) { x } else { y } } } }",
            false,
        );
        program
    }

    fn equations_for<'a>(eqs: &'a [DefEq], func: &str) -> Vec<&'a DefEq> {
        eqs.iter().filter(|e| e.func == func).collect()
    }

    fn succ(inner: Expr) -> Expr {
        Expr::Constructor { name: "Peano::Succ".to_string(), args: vec![inner] }
    }

    #[test]
    fn one_equation_per_leaf_with_patterns_guards_and_binders() {
        let program = program();
        let eqs = definitional_equations(&program);

        // flag: two leaves, no guards.
        let flag = equations_for(&eqs, "flag");
        assert_eq!(flag.len(), 2);
        assert!(flag.iter().all(|e| e.guards.is_empty()));

        // plus: the Succ leaf has the pattern as its first argument, the untouched
        // parameter as its second, and binders = the remaining parameter plus the
        // pattern variable.
        let plus = equations_for(&eqs, "plus");
        assert_eq!(plus.len(), 2);
        let succ_leaf = plus
            .iter()
            .find(|e| matches!(&e.args[0], Expr::Constructor { args, .. } if !args.is_empty()))
            .expect("the Succ leaf of plus");
        assert_eq!(succ_leaf.args, vec![succ(Expr::Var("x1".to_string())), Expr::Var("y".to_string())]);
        assert_eq!(succ_leaf.rhs, succ(Expr::Call { func: "plus".to_string(), args: vec![Expr::Var("x1".to_string()), Expr::Var("y".to_string())] }));
        let mut binders: Vec<_> = succ_leaf.binders.iter().map(|(n, _)| n.clone()).collect();
        binders.sort();
        assert_eq!(binders, vec!["x1".to_string(), "y".to_string()]);

        // pick: four leaves; the two under the `if` carry the guard and its negation,
        // and the matched variable is substituted by its pattern in the leaf.
        let pick = equations_for(&eqs, "pick");
        assert_eq!(pick.len(), 4);
        let guarded: Vec<_> = pick.iter().filter(|e| !e.guards.is_empty()).collect();
        assert_eq!(guarded.len(), 2);
        let guard_call = Expr::Call { func: "flag".to_string(), args: vec![Expr::Var("x1".to_string())] };
        assert!(guarded.iter().any(|e| e.guards == vec![guard_call.clone()] && e.rhs == succ(Expr::Var("x1".to_string()))));
        assert!(guarded.iter().any(|e| matches!(&e.guards[0], Expr::UnOp { op: UnOp::Not, expr } if **expr == guard_call)));
    }
}
