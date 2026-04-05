use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::Write;
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

pub fn append_result(path: &Path, result: &VerificationResult) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("create report dir {}", parent.display()))?;
    }
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .with_context(|| format!("open report {}", path.display()))?;
    serde_json::to_writer(&mut file, result).context("serialize verification result")?;
    file.write_all(b"\n")
        .context("terminate verification result line")?;
    Ok(())
}

pub fn load_results(path: &Path) -> anyhow::Result<Vec<VerificationResult>> {
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(err) => return Err(err).with_context(|| format!("read report {}", path.display())),
    };
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| serde_json::from_str(line).context("parse verification result"))
        .collect()
}
