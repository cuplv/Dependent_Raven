//! backend/src/epr_check.rs
//! 결정 가능성 보장을 위한 Sort Cycle Checker
//!
//! [KOR] SMT 솔버가 무한 매칭 루프에 빠지는 것을 방지하기 위해, NNF 변환이 완료된
//!       수식 내의 양화사 중첩(Forall -> Exists) 패턴을 분석하여 의존성 그래프를 만듭니다.
//!       그래프 내에 사이클(Cycle)이 존재할 경우 EPR 프래그먼트를 벗어난 것으로 간주하고 에러를 반환합니다.
//!
//! [ENG] To prevent SMT solvers from falling into infinite matching loops, this module
//!       analyzes quantifier nesting (Forall -> Exists) in NNF-transformed expressions
//!       to build a dependency graph. If a cycle is detected, it is considered outside
//!       the EPR fragment and an error is returned.

use frontend::ast::{Expr, BaseType, Ident, FunctionDef};
use petgraph::graphmap::DiGraphMap;
use petgraph::algo::tarjan_scc;
use std::collections::{HashSet, HashMap};

/// [KOR] 타입 의존성 사이클 경로를 나타냅니다.
/// [ENG] Represents a type dependency cycle path.
pub type Cycle = Vec<BaseType>;

/// [KOR] 목표 수식들과 전역 공리들을 모두 병합하여 Sort Cycle이 존재하는지 검사합니다.
/// 사이클이 없으면 Ok(()), 있으면 사이클 경로들의 리스트를 Err로 반환합니다.
///
/// 💡 [왜 전역 공리들을 함께 검사해야 하는가?]
/// 개별 수식에는 사이클이 없더라도, 여러 공리들이 합쳐지면 무한 루프가 발생할 수 있습니다.
/// 예를 들어, 공리 A(Person -> Dog)와 공리 B(Dog -> Person)가 동시에 존재하면
/// SMT 솔버는 값을 무한히 생성하며 영원히 끝나지 않게 됩니다(Undecidable).
/// 따라서 솔버가 보게 될 모든 수식을 하나의 거대한 그래프로 모아서 검사해야 합니다.
///
/// [ENG] Checks for Sort Cycles by merging all target expressions and global axioms.
/// Returns Ok(()) if no cycles, or Err with a list of cycle paths if any exist.
///
/// 💡 [Why merge global axioms?]
/// Even if individual expressions are acyclic, their combination might form an infinite loop.
/// For example, Axiom A (Person -> Dog) and Axiom B (Dog -> Person) together will cause
/// the SMT solver to generate values infinitely (Undecidable). Thus, we must aggregate
/// all expressions the solver will see into a single, massive dependency graph.
pub fn check_for_cycles(
    goals: &[Expr], 
    global_specs: &HashMap<Ident, FunctionDef>
) -> Result<(), Vec<Cycle>> {
    let mut graph = DiGraphMap::new();

    // 1-1. 목표 수식(Goals)들을 순회하며 간선 추가
    for goal_expr in goals {
        let mut active_foralls = HashSet::new();
        build_sort_graph(goal_expr, &mut graph, &mut active_foralls);
    }

    // 1-2. 전역 시그니처에 등록된 공리(Axioms/Function Bodies)들을 순회하며 간선 병합
    for (_, def) in global_specs {
        // 본문(body)이 존재하는 함수나 Lemma의 경우 그 자체가 솔버에 들어갈 공리임
        if let Some(body_expr) = &def.body {
            let mut active_foralls = HashSet::new();
            build_sort_graph(body_expr, &mut graph, &mut active_foralls);
        }
    }

    // 2. Petgraph의 Tarjan 알고리즘을 사용하여 강결합 컴포넌트(SCC) 탐색
    // SCC 중에 원소가 2개 이상이거나(서로 순환), 자기 자신을 도는 간선(Self-loop)이 있는 것이 사이클임
    let mut cycles = Vec::new();
    let sccs = tarjan_scc(&graph);

    for scc in sccs {
        if scc.len() > 1 {
            // 순환 사이클 (A -> B -> A)
            cycles.push(scc.into_iter().cloned().collect());
        } else if scc.len() == 1 {
            // Self-loop 확인 (A -> A)
            let node = scc[0];
            if graph.contains_edge(node, node) {
                cycles.push(vec![node.clone()]);
            }
        }
    }

    if cycles.is_empty() {
        Ok(())
    } else {
        Err(cycles)
    }
}

/// [KOR] AST를 하향식으로 순회하며 Forall에서 Exists로의 간선을 그래프에 추가합니다.
///       수식이 NNF 상태이므로 극성을 반전할 필요 없이 단순히 노드 타입만 확인합니다.
/// [ENG] Traverses the AST top-down, adding edges from Forall to Exists into the graph.
///       Since the expr is in NNF, we don't need to track polarity; just checking node types is enough.
fn build_sort_graph<'a>(
    expr: &'a Expr,
    graph: &mut DiGraphMap<&'a BaseType, ()>,
    active_foralls: &mut HashSet<&'a BaseType>,
) {
    match expr {
        Expr::Forall { binders, body } => {
            // 새로 진입하는 Forall 타입들을 기억해 둡니다.
            let mut newly_added = Vec::new();
            for (_, base_type) in binders {
                if active_foralls.insert(base_type) {
                    newly_added.push(base_type);
                }
                // 노드가 그래프에 존재하도록 등록
                graph.add_node(base_type);
            }

            // 하위 수식 탐색
            build_sort_graph(body, graph, active_foralls);

            // 스코프를 빠져나올 때 방금 추가한 타입들만 제거 (백트래킹)
            for base_type in newly_added {
                active_foralls.remove(base_type);
            }
        }
        Expr::Exists { binders, body } => {
            for (_, exists_type) in binders {
                graph.add_node(exists_type);
                // 현재 활성화된 모든 Forall 타입에서 이 Exists 타입으로 간선 추가
                for forall_type in active_foralls.iter() {
                    graph.add_edge(*forall_type, exists_type, ());
                }
            }

            // 하위 수식 탐색 (Exists는 active_foralls에 영향을 주지 않음)
            build_sort_graph(body, graph, active_foralls);
        }

        // 제어 흐름 분기
        Expr::If { cond, then_expr, else_expr } => {
            build_sort_graph(cond, graph, active_foralls);
            build_sort_graph(then_expr, graph, active_foralls);
            build_sort_graph(else_expr, graph, active_foralls);
        }
        Expr::Match { expr: target, arms } => {
            build_sort_graph(target, graph, active_foralls);
            for (_, arm_expr) in arms {
                build_sort_graph(arm_expr, graph, active_foralls);
            }
        }

        // Let 바인딩
        Expr::Let { bound_expr, body, .. } => {
            build_sort_graph(bound_expr, graph, active_foralls);
            build_sort_graph(body, graph, active_foralls);
        }

        // 이항/단항 연산자
        Expr::BinOp { left, right, .. } => {
            build_sort_graph(left, graph, active_foralls);
            build_sort_graph(right, graph, active_foralls);
        }
        Expr::UnOp { expr: inner, .. } => {
            build_sort_graph(inner, graph, active_foralls);
        }

        // 함수/생성자/관계식 호출
        Expr::Call { args, .. } | Expr::Constructor { args, .. } | Expr::ApplyRel { args, .. } => {
            for arg in args {
                build_sort_graph(arg, graph, active_foralls);
            }
        }
        Expr::Tuple(elems) => {
            for elem in elems {
                build_sort_graph(elem, graph, active_foralls);
            }
        }

        // 수동 인스턴스화 노드는 CEGQI 논문에 의해 Sort Cycle을 유발하지 않으므로,
        // 단순하게 내부 수식만 순회하거나 통과시킵니다.
        Expr::Instantiate(inner) => {
            build_sort_graph(inner, graph, active_foralls);
        }
        Expr::ExistentialBindings(bindings) => {
            for (_, e) in bindings {
                build_sort_graph(e, graph, active_foralls);
            }
        }

        // 리프 노드는 무시
        Expr::BoolConst(_) | Expr::Var(_) => {}
    }
}

/// [KOR] 사용자 친화적인 에러 메시지를 위해 사이클 경로를 문자열로 렌더링합니다.
/// [ENG] Renders the cycle path into a string for user-friendly error messages.
pub fn render_cycle(c: &Cycle) -> String {
    if c.len() == 1 {
        // Self-loop (e.g. Nat -> Nat)
        let name = render_base_type(&c[0]);
        format!("self-loop ⤷ {} ⤴", name)
    } else {
        let mut s = String::from("⤷ ");
        let mut first = true;
        for b in c {
            let name = render_base_type(b);
            if first {
                s.push_str(&name);
            } else {
                s.push_str(&format!(" → {}", name));
            }
            first = false;
        }
        s.push_str(" ⤴");
        s
    }
}

// BaseType을 렌더링하는 헬퍼 함수 (필요시 ast.rs 쪽에 구현하는 것이 좋음)
fn render_base_type(b: &BaseType) -> String {
    match b {
        BaseType::Unit => "Unit".to_string(),
        BaseType::Bool => "Bool".to_string(),
        BaseType::Custom(name) => name.clone(),
        BaseType::Tuple(ts) => {
            let inner: Vec<String> = ts.iter().map(render_base_type).collect();
            format!("({})", inner.join(", "))
        }
    }
}
