use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

pub fn print_report(results: &[VerificationResult]) -> bool {
    let mut success = true;
    for result in results {
        println!("{} {}", result.status, result.function);
        if !result.message.is_empty() {
            println!("  {}", result.message);
        }
        if let Some(bb) = result.basic_block {
            println!("  bb{bb}");
        }
        if !result.model.is_empty() {
            println!("  model: {:?}", result.model);
        }
        if !matches!(result.status, VerificationStatus::Pass) {
            success = false;
        }
    }
    success
}
