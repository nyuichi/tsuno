use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use tempfile::tempdir;

fn fixture_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/snapshots/fail")
        .join(format!("{name}.rs"))
}

fn run_fixture(name: &str) -> std::process::Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(fixture_file(name), root.join("src/main.rs")).expect("copy fixture");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    Command::new(env!("CARGO_BIN_EXE_tsuno-driver"))
        .current_dir(root)
        .arg(rustc)
        .args([
            "--crate-name",
            "fixture",
            "--edition=2024",
            "--crate-type",
            "bin",
            "--emit=metadata",
            "src/main.rs",
        ])
        .output()
        .expect("driver output")
}

#[test]
fn rejects_unused_invalid_lemma_during_prepass() {
    let output = run_fixture("rejects_unused_invalid_lemma_prepass");
    assert!(!output.status.success(), "fixture unexpectedly passed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("lemma `bad` assertion failed"),
        "unexpected stdout:\n{stdout}"
    );
}
