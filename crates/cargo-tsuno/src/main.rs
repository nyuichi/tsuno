#![feature(rustc_private)]

extern crate rustc_driver;

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use cargo_tsuno::cargo_api::CargoInvocation;
use clap::{Parser, Subcommand};
use tempfile::NamedTempFile;
use tsuno_driver::report::print_report;

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
        Commands::Verify { manifest_path } => run_cargo_check(&manifest_path),
    }
}

fn run_cargo_check(manifest_path: &Path) -> anyhow::Result<i32> {
    let invocation = CargoInvocation::discover(manifest_path)?;
    let report_file = NamedTempFile::new().context("create report file")?;
    let wrapper_exe = ensure_wrapper_binary()?;
    // Cargo drives compilation here so rustc can be wrapped and analyzed MIR can be collected.
    let output = Command::new("cargo")
        .current_dir(&invocation.workspace_root)
        .args(["check", "--offline", "--manifest-path"])
        .arg(&invocation.manifest_path)
        .env("TSUNO_REPORT_PATH", report_file.path())
        .env("RUSTC_WORKSPACE_WRAPPER", wrapper_exe)
        .output()
        .context("run cargo check")?;
    if !output.status.success() {
        bail!(
            "cargo check failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    print_report(report_file.path())
}

fn ensure_wrapper_binary() -> anyhow::Result<PathBuf> {
    let output = Command::new("cargo")
        .current_dir(tool_workspace_root())
        .args([
            "build",
            "--offline",
            "--package",
            "tsuno-driver",
            "--bin",
            "tsuno-driver",
        ])
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("TSUNO_REPORT_PATH")
        .output()
        .context("build tsuno-driver wrapper")?;
    if !output.status.success() {
        bail!(
            "cargo build failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let exe = env::current_exe().context("locate current executable")?;
    Ok(wrapper_executable(&exe))
}

fn wrapper_executable(exe: &Path) -> PathBuf {
    exe.with_file_name(format!("tsuno-driver{}", std::env::consts::EXE_SUFFIX))
}

fn tool_workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cargo-tsuno crate parent")
        .parent()
        .expect("workspace root")
        .to_path_buf()
}
