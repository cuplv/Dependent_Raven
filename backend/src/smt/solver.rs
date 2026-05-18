//! backend/src/smt/solver.rs
//! SMT 솔버(Z3 등)와의 통신 및 프로세스 관리를 담당하는 모듈

use easy_smt::{ContextBuilder};
use std::fs::File;

/// [KOR] SMT 솔버의 실행 환경 및 옵션을 설정하는 구조체입니다.
/// [ENG] A struct that configures the execution environment and options for the SMT solver.
#[derive(Debug)]
pub struct SolverConfig {
    program: String,
    args: Vec<String>,
    log_file: Option<String>, // SMT 쿼리를 저장할 파일명
}

impl SolverConfig {
    /// [KOR] 기본 솔버로 Z3를 사용합니다. CVC5보다 빠르고 설치가 쉽습니다.
    /// [ENG] Uses Z3 as the default solver. It's generally faster and easier to install than CVC5.
    pub fn default() -> Self {
        Self::z3()
    }

    /// [KOR] Z3 솔버를 SMT2 모드로 실행하기 위한 기본 설정을 반환합니다.
    /// [ENG] Returns the default configuration to run the Z3 solver in SMT2 mode.
    pub fn z3() -> Self {
        Self {
            program: "z3".to_string(),
            args: vec!["-smt2".to_string(), "-in".to_string()],
            log_file: None,
        }
    }

    /// [KOR] CVC5 솔버를 실행하기 위한 설정을 반환합니다. (기존 Ravencheck 호환용)
    /// [ENG] Returns the configuration to run the CVC5 solver. (For compatibility with legacy Ravencheck)
    pub fn cvc5() -> Self {
        Self {
            program: "cvc5".to_string(),
            args: vec![
                "--lang".to_string(), "smt2".to_string(),
                "--force-logic".to_string(), "ALL".to_string(),
                "--full-saturate-quant".to_string(),
                "--finite-model-find".to_string(),
            ],
            log_file: None,
        }
    }

    /// [KOR] SMT 쿼리를 파일로 저장(로깅)할 경로를 지정합니다.
    /// [ENG] Sets the path to save (log) the SMT queries.
    pub fn set_log_file(&mut self, filename: String) {
        self.log_file = Some(filename);
    }

    /// [KOR] 설정된 정보를 바탕으로 easy_smt::ContextBuilder를 생성합니다.
    /// [ENG] Creates an easy_smt::ContextBuilder based on the configured information.
    pub fn context_builder(&self) -> ContextBuilder {
        let mut builder = ContextBuilder::new();
        builder.solver(&self.program, &self.args);
        
        // [KOR] 로깅이 활성화되어 있다면, 솔버로 보내는 모든 S-Expr을 파일에도 똑같이 씁니다.
        // [ENG] If logging is enabled, mirror all S-Exprs sent to the solver to the file.
        if let Some(filename) = &self.log_file {
            if let Ok(file) = File::create(filename) {
                builder.replay_file(Some(file));
            }
        }
        
        builder
    }
}
