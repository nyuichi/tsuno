use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::Path;

use anyhow::Context;

use crate::diagnostic::VerificationResult;

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
