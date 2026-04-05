use std::fmt;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct VerificationResult {
    pub function: String,
    pub status: VerificationStatus,
    pub span: String,
    pub basic_block: Option<usize>,
    pub statement_index: Option<usize>,
    pub message: String,
    pub trace: Vec<String>,
    pub model: Vec<(String, String)>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum VerificationStatus {
    Pass,
    Fail,
    Unsupported,
}

impl fmt::Display for VerificationStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerificationStatus::Pass => write!(f, "PASS"),
            VerificationStatus::Fail => write!(f, "FAIL"),
            VerificationStatus::Unsupported => write!(f, "UNSUPPORTED"),
        }
    }
}
