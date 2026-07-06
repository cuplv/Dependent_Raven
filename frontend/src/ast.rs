//! frontend/src/ast.rs
//! F* 스타일의 Dependent Type Checking 및 백엔드 변환을 위한 통합 AST
//! Integrated AST for F* style Dependent Type Checking and Backend Compilation
//!
//! 이 파일은 프론트엔드(파서, 타입 체커)부터 백엔드(SMT 인코딩)까지
//! 프로젝트 전체를 관통하는 핵심 데이터 구조를 정의합니다.
//! This file defines the core data structures that span the entire project,
//! from the frontend (parser, type checker) to the backend (SMT encoding).

use std::collections::HashMap;

/// 식별자 타입 (Identifier Type)
/// 변수명, 함수명, 생성자명 등을 나타냅니다.
/// Represents variable names, function names, constructor names, etc.
pub type Ident = String;

// ==========================================
// Types (타입 시스템)
// ==========================================

/// 기본 데이터 타입 (Base Types)
/// 
/// [KOR] EPR(Extended Effectively Propositional) 프래그먼트를 준수하기 위해
/// 무한한 도메인을 갖는 내장 정수(Int) 타입은 지원하지 않습니다.
/// 오직 논리값(Bool), 튜플(Tuple), 그리고 사용자가 정의한 미해석 소트(Custom/Uninterpreted Sort)만 존재합니다.
/// 
/// [ENG] To comply with the EPR (Extended Effectively Propositional) fragment,
/// built-in infinite domains like Integer (Int) are NOT supported.
/// Only logical values (Bool), Tuples, and user-defined Uninterpreted Sorts (Custom) exist.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BaseType {
    /// 요소가 0개인 유닛 타입 (Empty tuple / Unit type)
    Unit,
    /// 참/거짓 논리 타입 (Logical boolean type)
    Bool,
    /// 튜플 타입 (Tuple type) - 예: (Bool, Custom("Nat"))
    /// 여러 값을 하나로 묶어 전달할 때 사용됩니다.
    Tuple(Vec<BaseType>),
    /// 사용자 정의 타입 및 미해석 소트 (User-defined or uninterpreted sort)
    /// e.g. "Nat", "List", "Heap"... declared as declare-sort in smt-encoding
    Custom(String),
}

impl BaseType {
    /// 유닛 타입을 반환하는 헬퍼 함수 / Returns the Unit type.
    pub fn unit() -> Self {
        BaseType::Unit
    }
}

/// 정제 타입 (Refinement Type)
/// 
/// [KOR] F* 스타일의 핵심입니다. 기본 타입에 논리적 조건(Predicate)을 부여합니다.
/// 예: `{ v: Nat | v > 0 }` (0보다 큰 자연수)
/// 
/// [ENG] The core of F* style types. Attaches a logical predicate to a base type.
/// Example: `{ v: Nat | v > 0 }` (a natural number strictly greater than 0)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefinedType {
    /// 바운드 변수 이름 (예: 'v') / Bound variable name (e.g., 'v')
    pub bound_var: Ident,
    /// 뼈대가 되는 기본 타입 / The underlying base type
    pub base: BaseType,
    /// 조건을 나타내는 논리식 / The logical predicate expression
    pub predicate: Expr,
}

/// 종속 함수 타입 (Dependent Function Type / Pi Type)
/// 
/// [KOR] 인자의 값에 따라 반환 타입이 달라질 수 있는 함수 타입입니다.
/// 예: `x: Nat -> { r: Nat | r > x }`
/// 
/// [ENG] A function type where the return type can depend on the value of the argument.
/// Example: `x: Nat -> { r: Nat | r > x }`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunType {
    /// 인자 이름 (이름을 알아야 반환 타입에서 참조할 수 있습니다) / Argument name
    pub param_name: Ident,
    /// 인자의 타입 / Argument type
    pub param_type: Box<Type>,
    /// 반환 타입 (인자 이름에 종속될 수 있음) / Return type (can depend on the argument name)
    pub ret_type: Box<Type>,
}

/// 전체 타입 시스템 (Comprehensive Type System)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// 조건이 없는 순수 기본 타입 / A pure base type without conditions
    Base(BaseType),
    /// 정제 타입 (조건이 붙은 타입) / A refined type with conditions
    Refined(RefinedType),
    /// 종속 함수 타입 / A dependent function type
    Arrow(FunType),
}

// ==========================================
// Operators (연산자)
// ==========================================

/// 이항 연산자 (Binary Operators)
/// 
/// [KOR] SMT 솔버의 LIA(Linear Integer Arithmetic) 이론을 배제하기 위해
/// 산술 연산자(+, -)와 대소 비교 연산자(<, >)는 여기서 제외되었습니다.
/// 
/// [ENG] To exclude SMT solver's LIA (Linear Integer Arithmetic) theories,
/// arithmetic (+, -) and relational (<, >) operators are excluded from here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    /// 동치 연산 (Equality) / ==
    Eq, 
    /// 비동치 연산 (Inequality) / !=
    Neq,          
    /// 논리합 (Logical OR) / ||
    Or, 
    /// 논리곱 (Logical AND) / &&
    And, 
    /// 논리적 함의 (Logical Implication) / => 
    Implies, 
}

/// 단항 연산자 (Unary Operators)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    /// 논리 부정 (Logical NOT) / !
    /// (NNF 변환 단계에서 트리의 가장 밑단으로 푸시됩니다 / Pushed to leaves during NNF)
    Not,
}

// ==========================================
// Patterns (패턴 매칭)
// ==========================================

/// 패턴 매칭을 위한 패턴 구조 (Patterns for matching)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// 와일드카드 (_) / Wildcard
    /// 값을 바인딩하지 않고 무시할 때 사용 / Used to ignore values without binding
    Wildcard,                           
    /// 변수 바인딩 (x) / Variable binding
    /// 매칭된 값을 새로운 변수에 할당할 때 사용 / Used to bind matched values to a new variable
    Ident(Ident),                       
    /// 생성자 패턴 (예: S(x'), Cons(hd, tl)) / Constructor pattern
    /// 귀납적 데이터 타입을 해체(Destructure)할 때 필수적 / Essential for destructuring inductive data types
    Constructor {
        name: Ident,
        args: Vec<Pattern>,
        /// [KOR] 생성자 필드들의 sort. 파서는 None으로 두고, 등록 시점의
        ///       resolve_pattern_types 패스가 datatypes 테이블을 조회해 채웁니다.
        ///       소비자(bind_pattern_vars 등)는 None을 만나면 패스 누락으로 간주하고 panic해야 합니다.
        /// [ENG] Sorts of the constructor's fields. The parser leaves this None;
        ///       the resolve_pattern_types pass fills it at registration time from
        ///       the datatypes table. Consumers must panic on None (missing pass).
        arg_types: Option<Vec<BaseType>>,
    },
    /// 튜플 패턴 (예: (x, y)) / Tuple pattern
    Tuple(Vec<Pattern>),                
}

// ==========================================
// Expressions (표현식 및 논리식)
// ==========================================

/// 프로그램 표현식 및 논리식 (Expressions & Logical Predicates)
/// 
/// [KOR] 이 열거형 하나가 프론트엔드의 계산식부터 SMT 백엔드의 논리식까지 모두 표현합니다.
/// ANF, NNF, RelAbs 변환 단계를 거치며 특정 노드(Call)는 사라지고 다른 노드(ApplyRel)가 추가됩니다.
/// 
/// [ENG] This single enum represents everything from frontend computations to SMT backend logical predicates.
/// Through ANF, NNF, and RelAbs transformations, certain nodes (Call) disappear and others (ApplyRel) emerge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// 논리 상수 (True / False) / Boolean constant
    BoolConst(bool),
    
    /// 변수 참조 / Variable reference
    Var(Ident),
    
    /// 튜플 생성 (e1, e2, ...) / Tuple creation
    Tuple(Vec<Expr>),

    /// 이항 연산 / Binary operation (&&, ||, ==, =>)
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    
    /// 단항 연산 / Unary operation (!)
    UnOp {
        op: UnOp,
        expr: Box<Expr>,
    },
    
    /// 조건문 / If-then-else
    /// [KOR] 제어 흐름 분기를 나타내며, 평가(Eval) 단계에서 분기가 확정되면 축약됩니다.
    /// [ENG] Represents control flow branching, which can be reduced if the condition is resolved during Eval.
    If {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    
    /// Let 바인딩 / Let binding (let pat = bound_expr in body)
    /// [KOR] ANF(A-Normal Form) 평탄화의 핵심 노드입니다. 중첩된 함수 호출이 Let 묶음으로 펼쳐집니다.
    /// [ENG] The core node for ANF (A-Normal Form) flattening. Nested calls are unrolled into Let bindings.
    Let {
        pat: Pattern,
        bound_expr: Box<Expr>,
        body: Box<Expr>,
    },
    
    /// 패턴 매칭 / Pattern matching (match expr { pat1 => e1, ... })
    /// [KOR] 사용자 주도 증명(F* style)에서 귀납법의 분기를 설정하는 데 사용됩니다.
    /// [ENG] Used to establish induction branches in user-driven proofs (F* style).
    Match {
        expr: Box<Expr>,
        arms: Vec<(Pattern, Expr)>,
    },
    
    /// 일반 함수 및 Lemma 호출 / Function and Lemma calls
    /// [KOR] 🌟 추상화 대상: 백엔드의 관계적 추상화(RelAbs) 단계에서 `forall v. f_rel(args, v)` 형태로 쪼개져 사라집니다.
    /// [ENG] 🌟 Target for abstraction: Disappears during RelAbs, split into relations like `forall v. f_rel(args, v)`.
    Call {
        func: Ident,
        args: Vec<Expr>,
    },

    /// 데이터 타입 생성자 호출 (예: Nat::Z, Nat::S(x)) / Data type constructor calls
    /// [KOR] 🌟 일반 함수와 달리, 이 노드는 SMT 솔버에서 데이터 생성자로 취급되며 단사성(Injectivity) 공리가 주입됩니다.
    /// [ENG] 🌟 Unlike normal functions, this is treated as a data constructor in SMT and injected with Injectivity axioms.
    Constructor {
        name: Ident,
        args: Vec<Expr>,
    },

    /// 관계식 적용 (백엔드 전용 노드) / Relational Predicate application (Backend only)
    /// [KOR] RelAbs 단계를 거치면 일반 `Call`은 사라지고 이 노드로 대체됩니다. 반드시 Bool을 반환하는 술어입니다.
    /// [ENG] Replaces `Call` after the RelAbs phase. It is a predicate that strictly returns Bool.
    ApplyRel {
        relation: Ident,
        args: Vec<Expr>,
    },

    /// 보편 양화사 (Forall) / Universal quantifier (∀)
    /// [KOR] binders에는 식별자와 "반드시 BaseType"이 들어갑니다. (EPR 규칙 상 BaseType만 정량화 가능)
    /// [ENG] Binders hold identifiers and strictly "BaseType"s (EPR rules allow quantifying only base sorts).
    Forall {
        binders: Vec<(Ident, BaseType)>,
        body: Box<Expr>,
    },
    
    /// 존재 양화사 (Exists) / Existential quantifier (∃)
    /// [KOR] 부정 극성(Negative polarity)의 함수가 관계식으로 쪼개질 때 주로 생성됩니다.
    /// [ENG] Primarily generated when negatively-polarized functions are split into relations.
    Exists {
        binders: Vec<(Ident, BaseType)>,
        body: Box<Expr>,
    },

    /// 수동 인스턴스화 (Manual Instantiation)
    /// [KOR] CEGQI 논문의 핵심. 특정 항(Ground Term)에 대한 로컬 전체성(Totality) 공리를 주입하기 위해 사용됩니다.
    ///       논리적으로는 True와 같지만, 백엔드의 ANF/RelAbs 파이프라인을 거치며 `exists r. f_rel(args, r)` 형태로 번역됩니다.
    /// [ENG] Core of the CEGQI paper. Used to inject a local totality axiom for a specific ground term.
    ///       Logically equivalent to True, but translates to `exists r. f_rel(args, r)` through the ANF/RelAbs pipeline.
    Instantiate(Box<Expr>),

    /// [KOR] Instantiate 노드가 ANF 평탄화를 거친 후의 모습입니다.
    ///       RelAbs 단계에서 무조건 Exists와 And 논리로 번역됩니다.
    /// [ENG] The ANF-flattened form of an Instantiate node.
    ///       Strictly translated into Exists and And logic during RelAbs.
    ExistentialBindings(Vec<(Ident, Expr)>),
}

// ==========================================
// Top-Level Module Payload (전체 프로그램 래퍼)
// ==========================================

/// 전체 검증 프로그램 구조체 (The Complete Verification Program Payload)
/// 
/// [KOR] 프론트엔드의 파싱/타입체킹이 끝나면, 이 구조체 하나에 모든 정보가 담겨 백엔드로 넘어갑니다.
/// 이 객체만 있으면 백엔드는 추가 파싱 없이 SMT-LIB2 코드를 끝까지 구워낼 수 있습니다.
/// 
/// [ENG] After frontend parsing/typechecking, all information is packed into this single struct and passed to the backend.
/// With this object, the backend can bake the SMT-LIB2 code end-to-end without further parsing.
#[derive(Debug, Clone)]
pub struct Program {
    /// 사용자 정의 데이터 타입 (예: enum Nat { Z, S(Nat) })
    /// [KOR] SMT 솔버에 `declare-datatypes`로 알려주기 위함.
    ///       형태: HashMap<타입명, Vec<(생성자명, 인자타입들)>>
    /// [ENG] Used to inform the SMT solver via `declare-datatypes`.
    ///       Format: HashMap<TypeName, Vec<(ConstructorName, ArgumentTypes)>>
    pub datatypes: HashMap<Ident, Vec<(Ident, Vec<BaseType>)>>, 
    
    /// 전역 함수 스펙 및 본문 
    /// [KOR] Eval(축약) 단계에서 본문을 치환하거나 SMT `declare-fun`을 할 때 조회합니다.
    /// [ENG] Looked up during Eval (reduction) for substitution or for SMT `declare-fun`.
    pub functions: HashMap<Ident, FunctionDef>,
    
    /// 증명해야 할 목표 명제들
    /// [KOR] 백엔드가 이 리스트를 순회하며 하나씩 SMT 솔버를 찔러 증명합니다.
    /// [ENG] The backend iterates through this list, probing the SMT solver to prove each goal.
    pub goals: Vec<Goal>,
}

/// 단일 함수의 정의 (Function Definition)
#[derive(Debug, Clone)]
pub struct FunctionDef {
    /// 함수의 전체 타입 스펙 (의존 타입 / Refinement 포함) / Full type spec (including dependencies/refinements)
    pub signature: Type,       
    /// 함수의 실제 본문 (미해석 함수이거나 인터페이스만 있으면 None) / The actual body (None if uninterpreted)
    pub body: Option<Expr>,    
    /// 재귀 함수 여부 / Recursion flag
    /// [KOR] Eval 단계에서 무한 루프(무한 인라이닝)를 막기 위한 플래그입니다.
    /// [ENG] Flag to prevent infinite loops (infinite inlining) during the Eval phase.
    pub is_recursive: bool,    
}

/// [ENG] A single Verification Condition (VC) combined with its strictly scoped instantiations.
#[derive(Debug, Clone)]
pub struct SubGoal {
    /// [ENG] The actual logical expression to be proven (Context => Target).
    pub property: Expr,
    /// [ENG] Instantiations (hints) strictly scoped to this specific VC.
    pub instantiations: Vec<Expr>,
}

/// 증명해야 할 목표 명제 (Verification Goal)
#[derive(Debug, Clone)]
pub struct Goal {
    /// 명제(정리)의 이름 / Name of the theorem/property
    pub name: Ident,
    /// 프론트엔드가 생성한 (그리고 백엔드가 가공할) 최종 논리식 / The final logical expression to be proven
    pub property: Expr,
    
    /// [ENG] Global instantiations explicitly provided by the user via `instantiate!(...)`.
    ///       These are extracted and collected during type checking, completely separate 
    ///       from the main VC to prevent code bloat and ensure they act as top-level axioms.
    pub instantiations: Vec<Expr>,
}
