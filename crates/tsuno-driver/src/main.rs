#![feature(rustc_private)]

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use clap::{Parser, Subcommand};
use tempfile::NamedTempFile;
use tsuno_driver::cargo_api::CargoInvocation;
use tsuno_driver::report::{VerificationStatus, load_results};
use tsuno_driver::wrapper::{REPORT_PATH_ENV, WRAPPER_ENV, maybe_run_wrapper};

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
    if let Some(code) = maybe_run_wrapper()? {
        return Ok(code);
    }
    let cli = Cli::parse();
    match cli.command {
        Commands::Verify { manifest_path } => verify_manifest(&manifest_path),
    }
}

fn verify_manifest(manifest_path: &Path) -> anyhow::Result<i32> {
    let invocation = CargoInvocation::discover(manifest_path)?;
    let report_file = NamedTempFile::new().context("create report file")?;
    let exe = env::current_exe().context("locate current executable")?;
    let output = Command::new("cargo")
        .current_dir(&invocation.workspace_root)
        .args(["check", "--offline", "--manifest-path"])
        .arg(&invocation.manifest_path)
        .env(WRAPPER_ENV, "1")
        .env(REPORT_PATH_ENV, report_file.path())
        .env("RUSTC_WORKSPACE_WRAPPER", exe)
        .output()
        .context("run cargo check")?;
    if !output.status.success() {
        bail!(
            "cargo check failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let results = load_results(report_file.path())?;
    let mut exit_code = 0;
    for result in &results {
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
