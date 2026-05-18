# 🚀 Project Milestone: F* Style Decidable Verification Framework

## 📌 Background & Goal
기존 Ravencheck의 난해한 CBPV(Call-By-Push-Value) 구조와 통제 불가능한 `Partial Eval`의 한계를 극복합니다. 
대신, DTC(Dependent Type Checker)가 완벽하게 통제된 증명 트리(VC)를 생성하고, 이를 평탄화하여 EPR(Extended Effectively Propositional) 논리로 안전하게 컴파일하는 **F* 스타일의 결정 가능(Decidable) SMT 백엔드를 독자적으로 재구축**합니다.

---

## 🛠️ Task 1. 파서 및 프론트엔드 보강 (`frontend/src/parser.rs` 및 `frontend/src/typecheck.rs`)

기존 Ravencheck의 속성(`#[assume]`, `#[verify]`)을 버리고, F* 스타일의 **정제 타입(Refinement Type)** 및 **언커리형 시그니처(Uncurried Signature)**를 지원하도록 파서와 프론트엔드를 대폭 수정해야 합니다.

- [x] **F* 스타일 시그니처 파싱**: `#[val((e1: u32, e2: u32) -> r: MySet { ... })]` 형태의 커스텀 매크로 토큰을 파싱하여 `frontend::ast::Type` AST로 완벽하게 변환.
- [x] **수식(Expr) 파서 업데이트**: `ast.rs`에서 산술 연산자(`+`, `<` 등)가 제거되었으므로, 파서가 이러한 연산자를 만났을 때 `BinOp` 대신 `Expr::Call { func: "add" }` 형태로 자동 치환하여 파싱하도록 수정.
- [x] **DTC(타입 체커)의 본문 분기 처리 로직**: `#[lemma]`의 증명 본문(`match` 문)을 따라가며 귀납적 가설(Inductive Hypothesis)을 환경에 추가하고, 최종적으로 VC 논리식(`Expr`)을 생성하는 로직 보강.

---

## 🛠️ Task 2. 절차적 매크로 구현 (`macros/src/lib.rs`)

복잡했던 수많은 매크로 명령들을 버리고, 오직 **타입 시그니처 추출과 백엔드 전송**이라는 핵심 역할에만 집중하는 가벼운 매크로 시스템을 구축합니다.

- [x] `#[ravencheck::module]` 매크로 진입점 구현.
- [x] 모듈 내 아이템 순회 및 분류:
  - `#[declare_types(u32)]` ➡️ `Program.datatypes` 에 미해석 소트로 등록.
  - `#[declare]` ➡️ 본문을 버리고 시그니처만 파싱하여 `body: None` 으로 `Program.functions` 에 등록.
  - `#[val]` (Refinement 존재) ➡️ 본문을 버리고, 시그니처에서 추출한 공리(Axiom)를 `Program.goals` 혹은 `axioms`에 추가.
  - `#[val]` (Refinement 없음) ➡️ 본문을 파싱하여 `body: Some(expr)` 로 저장. (이후 `eval` 단계에서 인라이닝 됨).
  - `#[lemma]` ➡️ 본문을 파싱 후, `frontend::typecheck`를 호출하여 생성된 증명 조건(VC)을 `Program.goals` 에 등록.
- [x] 조립된 `frontend::ast::Program` 객체를 `backend::smt::encode_and_solve(program)` 로 넘기는 런타임 `#[test]` 함수 코드 생성.

---

## 🛠️ Task 3. 부분 평가기 (Evaluator) 구현 (`backend/src/eval.rs`)

백엔드의 첫 관문입니다. SMT가 알지 못하는 함수(예: Refinement가 없는 `#[val]`)의 본문을 인라이닝하고, 불필요한 계산을 줄여줍니다. (예: `singleton(e) ➡️ insert(e, empty_set())`)

- [ ] `Program.functions`의 환경을 참조하는 평가기(Evaluator) 함수 `eval(expr: &Expr)` 구현.
- [ ] **Beta-Reduction**: `Call(f, args)` 노드 중 `body`가 존재하는 함수를 찾아, 인자를 본문에 치환(`substitute`)하고 평가.
- [ ] **생성자 평가 방지**: `Match` 대상이 결정된 생성자(예: `Nat::S`)인 경우에만 해당 브랜치 본문을 평가하고, 그 외에는 멈추어 구조를 보존.

---

## 🛠️ Task 4. 구조적 평탄화 (ANF) 구현 (`backend/src/anf.rs`)

관계적 추상화(Phase 6)를 수행하기 전, 중첩된 함수 호출(예: `union(union(a,b), b)`)을 SMT가 처리할 수 있는 평평한 형태로 풀어주는 단계입니다.

- [x] 트리를 순회하며 중첩된 `Call` 노드를 탐색.
- [x] `Call` 노드를 리프(Leaf) 노드로 분리하고, 임시 변수 바인딩(예: `let v = union(a, b) in union(v, b)`)을 생성하여 치환하는 `Let` 트랜스포머 구현.
- [x] *주의: 동치/논리 연산(`&&`, `||`, `==`)이나 생성자(`Constructor`)는 평탄화 대상에서 제외함.*

---

## 🛠️ Task 5. 부정 정규형 (NNF) 구현 (`backend/src/nnf.rs`)

관계적 추상화를 할 때 함수가 위치한 극성(Positive/Negative Position)을 파악할 수 있도록, 트리의 부정을 모두 안쪽으로 밀어넣습니다.

- [ ] `UnOp::Not` 노드를 만나면 드 모르간의 법칙(`!(A && B) ➡️ !A || !B`)을 적용.
- [ ] 양화사 반전 로직(`!(forall x. P(x)) ➡️ exists x. !P(x)`) 적용.
- [ ] 이 과정을 거쳐 트리의 가장 끝단(Leaf)인 관계식(Relation)이나 동치 연산(`==`)에만 부정 기호가 붙도록 강제.

---

## 🛠️ Task 6. 관계적 추상화 (Relational Abstraction) 구현 (`backend/src/relabs.rs`)

이 프로젝트의 **핵심 중의 핵심(Crown Jewel)**입니다. ANF와 NNF 처리가 완료된 수식에 남아있는 모든 미해석 함수 호출을 EPR 논리의 관계식(Relation)으로 쪼갭니다.

- [ ] AST 순회 중 `Let v = Call(f, args) in Body` 구조 탐색.
- [ ] **Positive Position**: `Forall(v). f_rel(args, v) IMPLIES Body` 로 변환.
- [ ] **Negative Position**: `Exists(v). f_rel(args, v) AND Body` 로 변환.
- [ ] `Call` 노드를 새로운 백엔드 전용 노드인 `ApplyRel(f_rel, args)` 로 치환.

---

## 🛠️ Task 7. 결정 가능성 보장 (Sort Cycle Check) (`backend/src/epr_check.rs`)

SMT 솔버가 무한 루프에 빠지지 않도록 양화사 중첩 구조를 그래프로 검사합니다. 이 단계를 통과해야 "Decidable" 하다고 말할 수 있습니다.

- [ ] RelAbs가 끝난 수식을 순회하며 `Exists(X) ... Forall(Y)` 패턴을 탐색하여 `Type(X) -> Type(Y)` 의존성 간선 생성.
- [ ] `petgraph` 라이브러리를 활용하여 사이클 탐지 (기존 Ravencheck 로직 이식 및 재사용).
- [ ] 사이클 발견 시 SMT 실행을 중단하고 컴파일 에러 반환.

---

## 🛠️ Task 8. SMT-LIB2 인코딩 및 CVC5 통신 (`backend/src/smt/mod.rs`)

모든 변환을 마친 순수 EPR 논리식(`Expr` AST)을 솔버가 이해할 수 있는 형태(`SExpr`)로 번역합니다.

- [ ] `easy-smt` 크레이트를 연동하여 커스텀 AST를 SMT-LIB2 문법으로 매핑.
- [ ] `Program` 구조체에 등록된 사용자 데이터 타입(`datatypes`) 및 `functions` 정보 읽기.
  - `#[declare_types(u32)]` ➡️ `(declare-sort u32 0)`.
  - `#[declare] type MySet` ➡️ `(declare-sort MySet 0)`.
  - 추상화된 관계식(`f_rel`) ➡️ `(declare-fun f_rel ... Bool)`.
- [ ] **데이터 타입 공리 주입**: 생성자 배타성, 단사성, Substructure 부분 순서 공리(Axioms) 생성 및 `(assert ...)` 주입 (기존 `constructions.rs` 적극 활용).
- [ ] 최종적으로 CVC5 서브프로세스를 띄워 `(check-sat)`을 실행하고 `Unsat` (검증 성공!) 또는 `Sat` (반례 발견) 판별 후 출력.