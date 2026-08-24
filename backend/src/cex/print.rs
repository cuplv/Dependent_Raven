//! [KOR] 소스 어휘 프리티 프린터.
//!
//! 반례 파일에 들어가는 모든 항은 사용자가 소스에 쓴 이름 그대로
//! SMT-LIB s-식으로 렌더링됩니다: 변수는 이름 그대로, 함수 호출은
//! `(add j k)`, 생성자는 enum 접두사를 뗀 variant 이름으로
//! (`Nat::S(x)` -> `(S x)`, `Nat::Z` -> `Z`).
//!
//! [ENG] Source-vocabulary pretty-printer.
//!
//! Every term that goes into the counterexample file is rendered as an
//! SMT-LIB s-expression using exactly the names the user wrote in the
//! source: variables as-is, function calls as `(add j k)`, constructors
//! by their variant name with the enum prefix stripped
//! (`Nat::S(x)` -> `(S x)`, `Nat::Z` -> `Z`).
//!
//! [KOR] 항 위치에 올 수 있는 노드는 Var / Call / Constructor / BoolConst
//! 뿐입니다. 그 외의 노드(Match, Let, 양화사, 백엔드 전용 노드 등)가
//! 들어오면 파이프라인 불변식이 깨진 것이므로 조용히 잘못 찍는 대신
//! panic으로 크게 실패합니다.
//! [ENG] Only Var / Call / Constructor / BoolConst can occur in term
//! position. Any other node (Match, Let, quantifiers, backend-only nodes,
//! ...) means a pipeline invariant broke, so we fail loudly with a panic
//! instead of silently misprinting.

use std::collections::BTreeSet;

use frontend::ast::{BaseType, Expr, Ident, Program};

use crate::smt::get_fun_types;

/// [KOR] 항을 소스 어휘의 SMT-LIB s-식 문자열로 렌더링합니다.
/// [ENG] Renders a term as an SMT-LIB s-expression string in source vocabulary.
pub fn print_term(e: &Expr) -> String {
    match e {
        Expr::Var(name) => name.clone(),
        Expr::BoolConst(b) => b.to_string(),
        Expr::Call { func, args } => print_application(func, args),
        Expr::Constructor { name, args } => print_application(variant_name(name), args),
        other => panic!(
            "counterexample printer: expression is not a source-level term: {:?}",
            other
        ),
    }
}

/// [KOR] 적용 형태를 찍습니다. 인자가 없으면 SMT-LIB 규칙대로 괄호 없이
///       이름만 씁니다 (예: `Z`).
/// [ENG] Prints an application. A nullary application is just the bare
///       name, per SMT-LIB convention (e.g. `Z`).
fn print_application(head: &str, args: &[Expr]) -> String {
    if args.is_empty() {
        return head.to_string();
    }
    let mut out = String::from("(");
    out.push_str(head);
    for arg in args {
        out.push(' ');
        out.push_str(&print_term(arg));
    }
    out.push(')');
    out
}

/// [KOR] 생성자 이름에서 enum 접두사를 뗀 variant 이름을 돌려줍니다
///       ("Nat::S" -> "S"). 벤치마크의 이름 규칙상(함수는 소문자,
///       variant는 대문자) 함수 이름과 충돌하지 않는다고 가정합니다.
/// [ENG] Returns the variant name of a constructor with the enum prefix
///       stripped ("Nat::S" -> "S"). Assumes no collision with function
///       names, which holds under the naming conventions used in the
///       benchmarks (lowercase functions, capitalized variants).
pub(super) fn variant_name(full: &str) -> &str {
    full.rsplit("::").next().unwrap_or(full)
}

/// [KOR] 생성자 이름의 enum 부분을 돌려줍니다 ("Nat::S" -> "Nat").
/// [ENG] Returns the enum part of a constructor name ("Nat::S" -> "Nat").
fn enum_name(full: &str) -> &str {
    full.split("::").next().unwrap_or(full)
}

/// [KOR] SMT-LIB/Z3에 이미 존재하는 소트 이름들. 사용자 datatype이 이
///       이름을 쓰면 (예: `enum List`) 그대로 선언할 수 없으므로 밑줄을
///       붙여 씁니다.
/// [ENG] Sort names that already exist in SMT-LIB/Z3. A user datatype with
///       one of these names (e.g. `enum List`) cannot be declared verbatim,
///       so it is written with a trailing underscore.
const RESERVED_SORTS: [&str; 7] = ["List", "Array", "Seq", "Set", "Int", "Real", "String"];

fn emitted_sort_name(name: &str) -> String {
    if RESERVED_SORTS.contains(&name) {
        format!("{}_", name)
    } else {
        name.to_string()
    }
}

/// [KOR] 소트를 소스 이름으로 렌더링합니다 ("Nat", "Bool"). Z3 내장 이름과
///       충돌하면 밑줄이 붙습니다. Unit/Tuple은 반례 파일의 선언에 나타날
///       수 없으므로 panic합니다.
/// [ENG] Renders a sort by its source name ("Nat", "Bool"), with a trailing
///       underscore on collision with a Z3 built-in. Unit/Tuple cannot
///       appear in counterexample declarations, so they panic.
fn sort_name(ty: &BaseType) -> String {
    match ty {
        BaseType::Custom(name) => emitted_sort_name(name),
        BaseType::Bool => "Bool".to_string(),
        other => panic!(
            "counterexample printer: sort has no source-level name: {:?}",
            other
        ),
    }
}

/// [KOR] 집합을 사람이 읽기 좋은 순서(대소문자 무시 사전순)로 정렬합니다.
///       HashMap 순회 순서에 의존하지 않는, 실행마다 같은 출력이 목적입니다.
/// [ENG] Orders a set case-insensitively for human-friendly, run-to-run
///       deterministic output independent of HashMap iteration order.
pub(super) fn sorted_ci(set: &BTreeSet<String>) -> Vec<&String> {
    let mut v: Vec<&String> = set.iter().collect();
    v.sort_by_key(|s| s.to_lowercase());
    v
}

/// [KOR] 항을 재귀적으로 걸어 사용된 함수 이름과 (생성자를 통해) 사용된
///       enum 이름을 수집합니다.
/// [ENG] Recursively walks a term collecting the function names used and
///       the enum names used (via constructors).
pub(super) fn collect_symbols(e: &Expr, funcs: &mut BTreeSet<String>, enums: &mut BTreeSet<String>) {
    match e {
        Expr::Var(_) | Expr::BoolConst(_) => {}
        Expr::Call { func, args } => {
            funcs.insert(func.clone());
            for arg in args {
                collect_symbols(arg, funcs, enums);
            }
        }
        Expr::Constructor { name, args } => {
            enums.insert(enum_name(name).to_string());
            for arg in args {
                collect_symbols(arg, funcs, enums);
            }
        }
        other => panic!(
            "counterexample printer: expression is not a source-level term: {:?}",
            other
        ),
    }
}

/// [KOR] 반례 파일의 선언 섹션을 만듭니다: 사용된 소트(declare-sort),
///       사용된 datatype의 모든 생성자, 사용된 함수, 그리고 goal의 입력
///       변수들. 생성자는 항에 나타난 것만이 아니라 datatype 전체를
///       선언합니다 -- 정의 주석 블록이 모든 생성자를 언급하므로 독자가
///       대조할 수 있어야 합니다. Unit 타입 입력(v_sub, _bind_*)은 증명
///       배관일 뿐이므로 걸러냅니다.
/// [ENG] Builds the declaration section of the counterexample file: the
///       sorts used (declare-sort), ALL constructors of every datatype
///       used, the functions used, and the goal's input variables. For a
///       used datatype we declare all of its constructors, not just the
///       ones occurring in terms -- the definitions comment block mentions
///       every constructor and the reader must be able to cross-check.
///       Unit-typed inputs (v_sub, _bind_*) are proof plumbing and are
///       filtered out.
pub fn print_declarations(
    program: &Program,
    terms: &[&Expr],
    inputs: &[(Ident, BaseType)],
) -> String {
    let mut funcs = BTreeSet::new();
    let mut enums = BTreeSet::new();
    for term in terms {
        collect_symbols(term, &mut funcs, &mut enums);
    }

    // [KOR] 선언해야 할 소트: 생성자의 enum + 사용된 함수 시그니처의 커스텀
    //       타입 + 입력의 커스텀 타입 + 선언될 생성자 필드의 커스텀 타입
    //       (예: Tree::Node의 Elem 필드처럼 항에는 안 보이는 소트).
    // [ENG] Sorts to declare: constructor enums + custom types in used
    //       function signatures + custom types of inputs + custom field
    //       types of the constructors we will declare (e.g. the Elem field
    //       of Tree::Node, which may not be visible in any term).
    let mut sorts: BTreeSet<String> = enums.clone();
    for func in &funcs {
        let def = program
            .functions
            .get(func)
            .unwrap_or_else(|| panic!("counterexample printer: unknown function '{}'", func));
        let (arg_types, out_type) = get_fun_types(&def.signature);
        for ty in arg_types.iter().chain(std::iter::once(&out_type)) {
            if let BaseType::Custom(name) = ty {
                sorts.insert(name.clone());
            }
        }
    }
    for (_, ty) in inputs {
        if let BaseType::Custom(name) = ty {
            sorts.insert(name.clone());
        }
    }
    for enum_nm in &enums {
        if let Some(variants) = program.datatypes.get(enum_nm) {
            for (_, field_types) in variants {
                for ty in field_types {
                    if let BaseType::Custom(name) = ty {
                        sorts.insert(name.clone());
                    }
                }
            }
        }
    }

    let mut out = String::new();
    for sort in sorted_ci(&sorts) {
        let emitted = emitted_sort_name(sort);
        if emitted != **sort {
            out.push_str(&format!(
                "; sort '{}' is written as '{}' below (the name collides with a Z3 built-in)\n",
                sort, emitted
            ));
        }
        out.push_str(&format!("(declare-sort {} 0)\n", emitted));
    }

    // [KOR] datatype인 소트마다 생성자 전부를 enum 선언 순서대로. (항이 아니라
    //       소트 기준입니다: 인자 없는 생성자는 인스턴스화 항에 절대 나타나지
    //       않지만 -- 수집기가 건너뜁니다 -- path condition이 참조할 수
    //       있습니다. 예: `n = Z`.)
    // [ENG] For each sort that is a datatype, all constructors in enum
    //       declaration order. (Keyed on sorts, not on terms: a nullary
    //       constructor never appears among the instantiated terms -- the
    //       collector skips them -- yet a path condition may reference it,
    //       e.g. `n = Z`.)
    for sort in sorted_ci(&sorts) {
        let Some(variants) = program.datatypes.get(sort.as_str()) else {
            continue;
        };
        let emitted = emitted_sort_name(sort);
        for (cons_name, field_types) in variants {
            if field_types.is_empty() {
                out.push_str(&format!("(declare-const {} {})\n", cons_name, emitted));
            } else {
                let fields: Vec<String> = field_types.iter().map(sort_name).collect();
                out.push_str(&format!(
                    "(declare-fun {} ({}) {})\n",
                    cons_name,
                    fields.join(" "),
                    emitted
                ));
            }
        }
    }

    for func in sorted_ci(&funcs) {
        let (arg_types, out_type) = get_fun_types(&program.functions[func].signature);
        let args: Vec<String> = arg_types.iter().map(sort_name).collect();
        out.push_str(&format!(
            "(declare-fun {} ({}) {})\n",
            func,
            args.join(" "),
            sort_name(&out_type)
        ));
    }

    out.push('\n');
    for (name, ty) in inputs {
        if matches!(ty, BaseType::Unit) {
            continue;
        }
        out.push_str(&format!("(declare-const {} {})\n", name, sort_name(ty)));
    }
    out
}

#[cfg(test)]
mod tests {
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

    #[test]
    fn variable_prints_as_its_name() {
        assert_eq!(print_term(&var("i_prime")), "i_prime");
    }

    #[test]
    fn bool_constants_print_as_smt_literals() {
        assert_eq!(print_term(&Expr::BoolConst(true)), "true");
        assert_eq!(print_term(&Expr::BoolConst(false)), "false");
    }

    #[test]
    fn nested_calls_print_as_sexprs() {
        // sub(sub(i, j), k)  ->  (sub (sub i j) k)
        let term = call("sub", vec![call("sub", vec![var("i"), var("j")]), var("k")]);
        assert_eq!(print_term(&term), "(sub (sub i j) k)");
    }

    #[test]
    fn nullary_constructor_prints_bare() {
        assert_eq!(print_term(&cons("Nat::Z", vec![])), "Z");
    }

    #[test]
    fn constructor_strips_enum_prefix() {
        // Nat::S(add(j_prime, k))  ->  (S (add j_prime k))
        let term = cons(
            "Nat::S",
            vec![call("add", vec![var("j_prime"), var("k")])],
        );
        assert_eq!(print_term(&term), "(S (add j_prime k))");
    }

    #[test]
    fn multi_argument_constructor() {
        // Tree::Node(mirror(r), e, mirror(l))  ->  (Node (mirror r) e (mirror l))
        let term = cons(
            "Tree::Node",
            vec![
                call("mirror", vec![var("r")]),
                var("e"),
                call("mirror", vec![var("l")]),
            ],
        );
        assert_eq!(print_term(&term), "(Node (mirror r) e (mirror l))");
    }

    #[test]
    #[should_panic(expected = "not a source-level term")]
    fn non_term_node_panics() {
        let not_a_term = Expr::Let {
            pat: frontend::ast::Pattern::Wildcard,
            bound_expr: Box::new(var("x")),
            body: Box::new(var("y")),
        };
        print_term(&not_a_term);
    }

    // ------------------------------------------------------------------
    // print_declarations
    // ------------------------------------------------------------------

    use std::collections::HashMap;

    use frontend::ast::{FunType, FunctionDef, Program, Type};

    fn nat() -> BaseType {
        BaseType::Custom("Nat".to_string())
    }

    /// [KOR] (T1, T2, ...) -> ret 모양의 커리된 함수 시그니처를 만듭니다.
    /// [ENG] Builds a curried function signature (T1, T2, ...) -> ret.
    fn signature(params: &[BaseType], ret: BaseType) -> Type {
        let mut ty = Type::Base(ret);
        for (i, p) in params.iter().enumerate().rev() {
            ty = Type::Arrow(FunType {
                param_name: format!("x{}", i),
                param_type: Box::new(Type::Base(p.clone())),
                ret_type: Box::new(ty),
            });
        }
        ty
    }

    fn fun_def(params: &[BaseType], ret: BaseType) -> FunctionDef {
        FunctionDef {
            signature: signature(params, ret),
            body: None,
            is_recursive: true,
        }
    }

    #[test]
    fn declarations_for_nat_arithmetic() {
        // prop_09 flavor: one datatype, two functions, Unit inputs filtered.
        let mut datatypes = HashMap::new();
        datatypes.insert(
            "Nat".to_string(),
            vec![("Z".to_string(), vec![]), ("S".to_string(), vec![nat()])],
        );
        let mut functions = HashMap::new();
        functions.insert("add".to_string(), fun_def(&[nat(), nat()], nat()));
        functions.insert("sub".to_string(), fun_def(&[nat(), nat()], nat()));
        let program = Program {
            datatypes,
            functions,
            goals: vec![],
        };

        // [KOR] 항에 생성자가 하나도 없어도 (수집기는 Z 같은 무인자 생성자를
        //       건너뜁니다) Nat이 datatype이므로 Z와 S가 선언되어야 합니다.
        // [ENG] Even with no constructor among the terms (the collector skips
        //       nullary ones like Z), Z and S must be declared because Nat is
        //       a datatype.
        let goal_term = call("sub", vec![call("sub", vec![var("i"), var("j")]), var("k")]);
        let rhs_term = call("sub", vec![var("i"), call("add", vec![var("j"), var("k")])]);
        let inputs = vec![
            ("i".to_string(), nat()),
            ("k".to_string(), nat()),
            ("j".to_string(), nat()),
            ("_bind_3".to_string(), BaseType::Unit),
            ("v_sub".to_string(), BaseType::Unit),
        ];

        let block = print_declarations(&program, &[&goal_term, &rhs_term], &inputs);
        assert_eq!(
            block,
            "(declare-sort Nat 0)\n\
             (declare-const Z Nat)\n\
             (declare-fun S (Nat) Nat)\n\
             (declare-fun add (Nat Nat) Nat)\n\
             (declare-fun sub (Nat Nat) Nat)\n\
             \n\
             (declare-const i Nat)\n\
             (declare-const k Nat)\n\
             (declare-const j Nat)\n"
        );
    }

    #[test]
    fn declarations_include_uninterpreted_field_sorts() {
        // prop_47 flavor: the Elem sort appears only as a Node field and an
        // input type, never as a datatype -- it must still be declared.
        let mut datatypes = HashMap::new();
        datatypes.insert(
            "Nat".to_string(),
            vec![("Z".to_string(), vec![]), ("S".to_string(), vec![nat()])],
        );
        let tree = || BaseType::Custom("Tree".to_string());
        let elem = || BaseType::Custom("Elem".to_string());
        datatypes.insert(
            "Tree".to_string(),
            vec![
                ("Leaf".to_string(), vec![]),
                ("Node".to_string(), vec![tree(), elem(), tree()]),
            ],
        );
        let mut functions = HashMap::new();
        functions.insert("height".to_string(), fun_def(&[tree()], nat()));
        functions.insert("mirror".to_string(), fun_def(&[tree()], tree()));
        let program = Program {
            datatypes,
            functions,
            goals: vec![],
        };

        let lhs = call("height", vec![call("mirror", vec![var("t")])]);
        let node = cons(
            "Tree::Node",
            vec![
                call("mirror", vec![var("r")]),
                var("e"),
                call("mirror", vec![var("l")]),
            ],
        );
        let inputs = vec![
            ("t".to_string(), tree()),
            ("l".to_string(), tree()),
            ("e".to_string(), elem()),
            ("r".to_string(), tree()),
        ];

        let block = print_declarations(&program, &[&lhs, &node], &inputs);
        assert_eq!(
            block,
            "(declare-sort Elem 0)\n\
             (declare-sort Nat 0)\n\
             (declare-sort Tree 0)\n\
             (declare-const Z Nat)\n\
             (declare-fun S (Nat) Nat)\n\
             (declare-const Leaf Tree)\n\
             (declare-fun Node (Tree Elem Tree) Tree)\n\
             (declare-fun height (Tree) Nat)\n\
             (declare-fun mirror (Tree) Tree)\n\
             \n\
             (declare-const t Tree)\n\
             (declare-const l Tree)\n\
             (declare-const e Elem)\n\
             (declare-const r Tree)\n"
        );
    }

    #[test]
    fn reserved_sort_name_gets_underscore_and_note() {
        // A user datatype named `List` collides with Z3's built-in List sort.
        let mut datatypes = HashMap::new();
        let list = || BaseType::Custom("List".to_string());
        let elem = || BaseType::Custom("Elem".to_string());
        datatypes.insert(
            "List".to_string(),
            vec![
                ("Nil".to_string(), vec![]),
                ("Cons".to_string(), vec![elem(), list()]),
            ],
        );
        let mut functions = HashMap::new();
        functions.insert("app".to_string(), fun_def(&[list(), list()], list()));
        let program = Program {
            datatypes,
            functions,
            goals: vec![],
        };

        let term = call("app", vec![var("x"), var("y")]);
        let inputs = vec![("x".to_string(), list()), ("h".to_string(), elem())];

        let block = print_declarations(&program, &[&term], &inputs);
        assert_eq!(
            block,
            "(declare-sort Elem 0)\n\
             ; sort 'List' is written as 'List_' below (the name collides with a Z3 built-in)\n\
             (declare-sort List_ 0)\n\
             (declare-const Nil List_)\n\
             (declare-fun Cons (Elem List_) List_)\n\
             (declare-fun app (List_ List_) List_)\n\
             \n\
             (declare-const x List_)\n\
             (declare-const h Elem)\n"
        );
    }
}
