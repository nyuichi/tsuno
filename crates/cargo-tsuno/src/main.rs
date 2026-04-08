use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use camino::Utf8PathBuf;
use clap::Parser;
use serde::Deserialize;

#[derive(Parser)]
struct Cli {}

fn main() {
    match try_main() {
        Ok(code) => std::process::exit(code),
        Err(err) => {
            eprintln!("{err:#}");
            std::process::exit(1);
        }
    }
}

fn try_main() -> anyhow::Result<i32> {
    Cli::parse();
    let manifest_path = find_manifest_path_from_current_dir()?;
    let manifest_path = std::fs::canonicalize(manifest_path).context("resolve manifest path")?;
    let invocation = CargoInvocation::discover(&manifest_path)?;
    verify(&invocation)
}

#[derive(Debug, Clone)]
struct CargoInvocation {
    manifest_path: Utf8PathBuf,
    workspace_root: Utf8PathBuf,
}

#[derive(Debug, Deserialize)]
struct Metadata {
    workspace_root: String,
}

impl CargoInvocation {
    fn discover(manifest_path: &Path) -> anyhow::Result<Self> {
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

fn verify(invocation: &CargoInvocation) -> anyhow::Result<i32> {
    let wrapper_exe = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name(format!("tsuno-driver{}", std::env::consts::EXE_SUFFIX));

    // Cargo drives compilation here so rustc can be wrapped and analyzed MIR can be collected.
    let status = Command::new("cargo")
        .current_dir(&invocation.workspace_root)
        .args(["check", "--offline", "--quiet", "--manifest-path"])
        .arg(&invocation.manifest_path)
        .env("RUSTC_WORKSPACE_WRAPPER", wrapper_exe)
        .spawn()
        .context("run cargo check")?
        .wait()
        .context("wait for cargo check")?;

    Ok(status.code().unwrap_or(1))
}

fn find_manifest_path_from_current_dir() -> anyhow::Result<PathBuf> {
    let current_dir = std::env::current_dir().context("get current dir")?;
    for dir in current_dir.ancestors() {
        let manifest_path = dir.join("Cargo.toml");
        if manifest_path.is_file() {
            return Ok(manifest_path);
        }
    }
    bail!("could not find Cargo.toml in current directory or ancestors");
}

#[cfg(test)]
mod tests {
    use super::{Cli, find_manifest_path_from_current_dir};
    use std::fs;
    use std::path::{Path, PathBuf};

    use clap::Parser;
    use tempfile::tempdir;

    struct CurrentDirGuard {
        previous_dir: PathBuf,
    }

    impl CurrentDirGuard {
        fn set_to(path: &Path) -> Self {
            let previous_dir = std::env::current_dir().expect("current dir");
            std::env::set_current_dir(path).expect("set current dir");
            Self { previous_dir }
        }
    }

    impl Drop for CurrentDirGuard {
        fn drop(&mut self) {
            std::env::set_current_dir(&self.previous_dir).expect("restore current dir");
        }
    }

    #[test]
    fn parses_without_subcommand() {
        Cli::try_parse_from(["cargo-tsuno"]).expect("parse cli");
    }

    #[test]
    fn rejects_verify_subcommand() {
        assert!(Cli::try_parse_from(["cargo-tsuno", "verify"]).is_err());
    }

    #[test]
    fn finds_manifest_in_current_dir_ancestor_chain() {
        let temp_dir = tempdir().expect("tempdir");
        let manifest_path = temp_dir.path().join("Cargo.toml");
        fs::write(
            &manifest_path,
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .expect("write manifest");
        let nested_dir = temp_dir.path().join("nested").join("deeper");
        fs::create_dir_all(&nested_dir).expect("create nested dir");
        let _guard = CurrentDirGuard::set_to(&nested_dir);

        let found_manifest_path = find_manifest_path_from_current_dir().expect("find manifest");

        assert_eq!(
            fs::canonicalize(found_manifest_path).expect("canonicalize found manifest"),
            fs::canonicalize(manifest_path).expect("canonicalize expected manifest")
        );
    }
}
