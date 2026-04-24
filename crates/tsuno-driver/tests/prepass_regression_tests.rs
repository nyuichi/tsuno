use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use tempfile::tempdir;

fn fixture_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/snapshots/fail")
        .join(format!("{name}.rs"))
}

fn pass_fixture_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/snapshots/pass")
        .join(format!("{name}.rs"))
}

fn prepass_fixture_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/prepass")
        .join(format!("{name}.rs"))
}

fn run_fixture(name: &str) -> std::process::Output {
    run_fixture_file(fixture_file(name))
}

fn run_prepass_fixture(name: &str) -> std::process::Output {
    run_fixture_file(prepass_fixture_file(name))
}

fn run_fixture_file(path: PathBuf) -> std::process::Output {
    run_fixture_file_with_args(
        path,
        &[
            "--crate-name",
            "fixture",
            "--edition=2024",
            "--crate-type",
            "bin",
            "--emit=metadata",
            "src/main.rs",
        ],
    )
}

fn run_fixture_file_with_args(path: PathBuf, args: &[&str]) -> std::process::Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(path, root.join("src/main.rs")).expect("copy fixture");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    Command::new(env!("CARGO_BIN_EXE_tsuno-driver"))
        .current_dir(root)
        .arg(rustc)
        .args(args)
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

#[test]
fn reports_multiple_function_prepass_errors_before_verification() {
    let output = run_prepass_fixture("reports_multiple_function_prepass_errors");
    assert!(!output.status.success(), "fixture unexpectedly passed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("UNSUPPORTED first_bad"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("duplicate spec binding `X` in //@ let"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("UNSUPPORTED second_bad"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("unresolved binding `Y` in function contract"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("PASS main"),
        "verification should not run after prepass errors:\n{stdout}"
    );
}

#[test]
fn rejects_invalid_ghosts_without_toplevel_functions() {
    let output = run_fixture_file_with_args(
        prepass_fixture_file("rejects_invalid_ghosts_without_toplevel_functions"),
        &[
            "--crate-name",
            "fixture",
            "--edition=2024",
            "--crate-type",
            "lib",
            "--emit=metadata",
            "src/main.rs",
        ],
    );
    assert!(!output.status.success(), "fixture unexpectedly passed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("lemma `bad` assertion failed"),
        "unexpected stdout:\n{stdout}"
    );
}

#[test]
fn prelude_definitions_are_available_by_default() {
    let output = run_fixture_file(pass_fixture_file("uses_prelude_definitions"));
    assert!(
        output.status.success(),
        "unexpected stdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn named_lemma_parameter_is_admissible() {
    let output = run_fixture_file(pass_fixture_file("named_lemma_parameter_is_admissible"));
    assert!(
        output.status.success(),
        "unexpected stdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn redefining_prelude_definition_is_rejected() {
    let output = run_prepass_fixture("rejects_duplicate_prelude_definition");
    assert!(!output.status.success(), "fixture unexpectedly passed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("duplicate pure function name"),
        "unexpected stdout:\n{stdout}"
    );
}

#[test]
fn complex_lemma_assumption_is_admitted_during_prepass() {
    let output = run_prepass_fixture("allows_complex_lemma_assumption");
    assert!(
        output.status.success(),
        "unexpected stdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn rejects_unknown_existential_lemma_assertion_during_prepass() {
    let output = run_prepass_fixture("rejects_unknown_existential_lemma_assertion");
    assert!(!output.status.success(), "fixture unexpectedly passed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("UNSUPPORTED prepass"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("expected a spec expression"),
        "unexpected stdout:\n{stdout}"
    );
}
