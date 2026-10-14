//! [KOR] 기호적 경계(symbolic frontier): 정의를 goal의 분기가 고정한 생성자 모양에
//!       맞춰 기호적으로 전개하여, 질의에 없는 적용 항을 자동으로 인스턴스화합니다.
//!       solver 모델은 읽지 않습니다. 계획: `doc/auto_instantiation_plan.md`.
//!       현재 단계: 2 (모양 환경), 3 (한 단계 전개), 4 (한 라운드의 후보).
//! [ENG] The symbolic frontier: automatic instantiation by unfolding definitions
//!       against the constructor shapes a goal's branch fixes, never against a
//!       solver model. Plan: `doc/auto_instantiation_plan.md`. Implemented so
//!       far: step 2 (the shape environment), step 3 (one unfolding step), step 4
//!       (one round's candidates).

pub mod candidates;
pub mod shape;
pub mod unroll;
