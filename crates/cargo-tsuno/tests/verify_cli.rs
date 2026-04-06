use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::tempdir;

fn fixture_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/verify_cli")
        .join(format!("{name}.rs"))
}

fn fixture_names() -> Vec<String> {
    let mut names = Vec::new();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/verify_cli");
    for entry in fs::read_dir(dir).expect("read fixture dir") {
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

fn run_fixture(name: &str) -> Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    let tsuno = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tsuno");
    fs::write(
        root.join("Cargo.toml"),
        format!(
            r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2024"

[dependencies]
tsuno = {{ path = "{}" }}
"#,
            tsuno.display()
        ),
    )
    .expect("manifest");
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(fixture_file(name), root.join("src/main.rs")).expect("copy fixture");

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

fn assert_cli_snapshot(name: &str, output: &Output) {
    insta::assert_snapshot!(name, snapshot_output(output));
}

#[test]
fn verify_cli_fixtures() {
    for name in fixture_names() {
        let output = run_fixture(&name);
        assert_cli_snapshot(&name, &output);
    }
}
