use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use camino::Utf8PathBuf;
use serde::Deserialize;

#[derive(Debug, Clone)]
pub struct CargoInvocation {
    pub manifest_path: Utf8PathBuf,
    pub workspace_root: Utf8PathBuf,
}

#[derive(Debug, Deserialize)]
struct Metadata {
    workspace_root: String,
}

impl CargoInvocation {
    pub fn discover(manifest_path: &Path) -> anyhow::Result<Self> {
        let output = Command::new("cargo")
            .args([
                "metadata",
                "--offline",
                "--format-version",
                "1",
                "--no-deps",
                "--manifest-path",
            ])
            .arg(manifest_path)
            .output()
            .context("run cargo metadata")?;
        if !output.status.success() {
            bail!(
                "cargo metadata failed:\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let metadata: Metadata =
            serde_json::from_slice(&output.stdout).context("parse cargo metadata")?;
        Ok(Self {
            manifest_path: Utf8PathBuf::from_path_buf(PathBuf::from(manifest_path))
                .map_err(|path| anyhow::anyhow!("non utf8 manifest path: {}", path.display()))?,
            workspace_root: Utf8PathBuf::from(metadata.workspace_root),
        })
    }
}
