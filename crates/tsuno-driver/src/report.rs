use std::fmt;
use std::fs;
use std::path::Path;

use anyhow::Context;
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

pub fn print_report(path: &Path) -> anyhow::Result<i32> {
    let results = {
        let text = match fs::read_to_string(path) {
            Ok(text) => text,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => String::new(),
            Err(err) => return Err(err).with_context(|| format!("read report {}", path.display())),
        };
        text.lines()
            .filter(|line| !line.trim().is_empty())
            .map(|line| serde_json::from_str(line).context("parse verification result"))
            .collect::<anyhow::Result<Vec<VerificationResult>>>()?
    };
    let mut exit_code = 0;
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
            exit_code = 1;
        }
    }
    Ok(exit_code)
}
