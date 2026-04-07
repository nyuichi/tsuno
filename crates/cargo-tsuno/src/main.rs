use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use camino::Utf8PathBuf;
use clap::{Parser, Subcommand};
use serde::Deserialize;

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Verify {
        #[arg(long)]
        manifest_path: PathBuf,
    },
}

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
    let cli = Cli::parse();
    match cli.command {
        Commands::Verify { manifest_path } => {
            let invocation = CargoInvocation::discover(&manifest_path)?;
            verify(&invocation)
        }
    }
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
