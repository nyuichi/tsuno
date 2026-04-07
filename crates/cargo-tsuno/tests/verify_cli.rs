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
        .join("tests/fixtures/verify_cli")
        .join(kind.dir_name())
}

fn fixture_file(kind: FixtureKind, name: &str) -> PathBuf {
    fixture_dir(kind).join(format!("{name}.rs"))
}

fn fixture_names(kind: FixtureKind) -> Vec<String> {
    let mut names = Vec::new();
    for entry in fs::read_dir(fixture_dir(kind)).expect("read fixture dir") {
        let entry = entry.expect("fixture entry");
        if !entry.file_type().expect("fixture type").is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
            continue;
        }
        names.push(
            path.file_stem()
                .and_then(|stem| stem.to_str())
                .expect("fixture stem")
                .to_owned(),
        );
    }
    names.sort();
    names
}

fn run_fixture(kind: FixtureKind, name: &str) -> Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    let tsuno = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tsuno");
    let manifest = format!(
        r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2024"

[dependencies]
tsuno = {{ path = "{}" }}
"#,
        tsuno.display()
    );
    fs::write(root.join("Cargo.toml"), manifest).expect("manifest");
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(fixture_file(kind, name), root.join("src/main.rs")).expect("copy fixture");

    Command::new(env!("CARGO_BIN_EXE_cargo-tsuno"))
        .args(["verify", "--manifest-path"])
        .arg(root.join("Cargo.toml"))
        .output()
        .expect("driver output")
}

fn snapshot_output(output: &Output) -> String {
    format!(
        "status: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    )
}

fn assert_cli_snapshot(kind: FixtureKind, name: &str, output: &Output) {
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path(format!("fixtures/verify_cli/{}", kind.dir_name()));
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| {
        insta::assert_snapshot!(name, snapshot_output(output));
    });
}

#[test]
fn verify_cli_pass_fixtures() {
    for name in fixture_names(FixtureKind::Pass) {
        let output = run_fixture(FixtureKind::Pass, &name);
        assert_cli_snapshot(FixtureKind::Pass, &name, &output);
    }
}

#[test]
fn verify_cli_fail_fixtures() {
    for name in fixture_names(FixtureKind::Fail) {
        let output = run_fixture(FixtureKind::Fail, &name);
        assert_cli_snapshot(FixtureKind::Fail, &name, &output);
    }
}
