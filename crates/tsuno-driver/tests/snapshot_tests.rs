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

fn copy_fixture_support_dir(src: &Path, dst: &Path) {
    if !src.exists() {
        return;
    }
    for entry in fs::read_dir(src).expect("read fixture support dir") {
        let entry = entry.expect("fixture support entry");
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        if entry.file_type().expect("fixture support type").is_dir() {
            fs::create_dir_all(&dst_path).expect("create fixture support subdir");
            copy_fixture_support_dir(&src_path, &dst_path);
        } else {
            fs::copy(src_path, dst_path).expect("copy fixture support file");
        }
    }
}

fn run_fixture(kind: FixtureKind, name: &str) -> Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    let src_dir = root.join("src");
    fs::create_dir(&src_dir).expect("src dir");
    fs::copy(fixture_file(kind, name), src_dir.join("main.rs")).expect("copy fixture");
    copy_fixture_support_dir(&fixture_dir(kind).join(name), &src_dir);
    let external_spec_fixture_dir = fixture_dir(kind).join(format!("{name}.specs"));
    let external_spec_root = root.join("specs");
    if external_spec_fixture_dir.exists() {
        fs::create_dir(&external_spec_root).expect("create external spec root");
        copy_fixture_support_dir(&external_spec_fixture_dir, &external_spec_root);
    }
    let sidecar = fixture_dir(kind).join(format!("{name}.rs.tsuno"));
    if sidecar.exists() {
        fs::copy(sidecar, src_dir.join("main.rs.tsuno")).expect("copy sidecar fixture");
    }

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let mut command = Command::new(env!("CARGO_BIN_EXE_tsuno-driver"));
    command.current_dir(root).arg(rustc).args([
        "--crate-name",
        "fixture",
        "--edition=2024",
        "--crate-type",
        "bin",
        "--emit=metadata",
        "src/main.rs",
    ]);
    if external_spec_fixture_dir.exists() {
        command
            .env("TSUNO_SUBJECT_ROOT", root)
            .env("TSUNO_SPEC_ROOT", &external_spec_root);
    }
    let output = command.output().expect("driver output");

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
