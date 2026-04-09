use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::tempdir;

#[derive(Clone, Copy)]
enum FixtureKind {
    Pass,
    Fail,
}

impl FixtureKind {
    fn dir_name(self) -> &'static str {
        match self {
            FixtureKind::Pass => "pass",
            FixtureKind::Fail => "fail",
        }
    }
}

fn fixture_dir(kind: FixtureKind) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/snapshots")
        .join(kind.dir_name())
}

fn fixture_file(kind: FixtureKind, name: &str) -> PathBuf {
    fixture_dir(kind).join(format!("{name}.rs"))
}

fn run_fixture(kind: FixtureKind, name: &str) -> Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(fixture_file(kind, name), root.join("src/main.rs")).expect("copy fixture");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let output = Command::new(env!("CARGO_BIN_EXE_tsuno-driver"))
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
        .expect("driver output");

    Output {
        status: output.status,
        stdout: output.stdout,
        stderr: Vec::new(),
    }
}

fn snapshot_status(output: &Output) -> Option<i32> {
    if output.status.success() {
        Some(0)
    } else {
        Some(1)
    }
}

fn snapshot_output(output: &Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    format!(
        "status: {:?}\nstdout:\n{}\nstderr:\n{}",
        snapshot_status(output),
        stdout,
        stderr,
    )
}

fn assert_cli_snapshot(kind: FixtureKind, name: &str, output: &Output) {
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path(format!("fixtures/snapshots/{}", kind.dir_name()));
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| {
        insta::assert_snapshot!(name, snapshot_output(output));
    });
}

include!(concat!(env!("OUT_DIR"), "/generated_snapshot_tests.rs"));
