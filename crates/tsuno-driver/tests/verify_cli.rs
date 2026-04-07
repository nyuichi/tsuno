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

fn redact_basic_blocks(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut redacted = String::with_capacity(text.len());
    let mut index = 0;

    while index < bytes.len() {
        if index + 2 <= bytes.len() && bytes[index] == b'b' && bytes[index + 1] == b'b' {
            let mut end = index + 2;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > index + 2 {
                redacted.push_str("bb<N>");
                index = end;
                continue;
            }
        }
        redacted.push(bytes[index] as char);
        index += 1;
    }

    redacted
}

fn redact_model_details(text: &str) -> String {
    let mut redacted = String::with_capacity(text.len());
    for (index, line) in text.split_terminator('\n').enumerate() {
        if index > 0 {
            redacted.push('\n');
        }
        if line.starts_with("  model: [(\"model\", ") {
            redacted.push_str("  model: [(\"model\", \"<redacted>\")]");
        } else {
            redacted.push_str(line);
        }
    }
    if text.ends_with('\n') {
        redacted.push('\n');
    }
    redacted
}

fn run_fixture(kind: FixtureKind, name: &str) -> Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    let manifest = r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2024"
"#
    .to_string();
    fs::write(root.join("Cargo.toml"), manifest).expect("manifest");
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(fixture_file(kind, name), root.join("src/main.rs")).expect("copy fixture");

    let output = Command::new("cargo")
        .current_dir(root)
        .args(["check", "--offline", "--manifest-path"])
        .arg(root.join("Cargo.toml"))
        .env(
            "RUSTC_WORKSPACE_WRAPPER",
            env!("CARGO_BIN_EXE_tsuno-driver"),
        )
        .output()
        .expect("cargo output");

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
    let stdout = redact_model_details(&redact_basic_blocks(&String::from_utf8_lossy(
        &output.stdout,
    )));
    let stderr = redact_model_details(&redact_basic_blocks(&String::from_utf8_lossy(
        &output.stderr,
    )));
    format!(
        "status: {:?}\nstdout:\n{}\nstderr:\n{}",
        snapshot_status(output),
        stdout,
        stderr,
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

include!(concat!(env!("OUT_DIR"), "/verify_cli_tests.rs"));

#[cfg(test)]
mod tests {
    use super::{redact_basic_blocks, redact_model_details};

    #[test]
    fn redacts_basic_block_numbers() {
        assert_eq!(
            redact_basic_blocks("bb15\n  bb2\nno change"),
            "bb<N>\n  bb<N>\nno change"
        );
    }

    #[test]
    fn redacts_model_details() {
        assert_eq!(
            redact_model_details("  model: [(\"model\", \"arg_6_2 -> 0\\n\")]"),
            "  model: [(\"model\", \"<redacted>\")]"
        );
    }
}
