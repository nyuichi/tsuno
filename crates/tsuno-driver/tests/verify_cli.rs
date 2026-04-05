use std::fs;
use std::path::Path;
use std::process::{Command, Output};

use tempfile::tempdir;

fn run_fixture(main_rs: &str) -> Output {
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
    fs::write(root.join("src/main.rs"), main_rs).expect("main");

    Command::new(env!("CARGO_BIN_EXE_tsuno-driver"))
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
fn verifies_a_trivial_assertion_fixture() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn ok(x: i32) {
    tsuno::assert!(x == x);
}

fn main() {}
"#,
    );
    assert_cli_snapshot("verifies_a_trivial_assertion_fixture", &output);
}

#[test]
fn reports_failing_assertion() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn bad(x: i32) {
    tsuno::assert!(x == 0);
}

fn main() {}
"#,
    );
    assert_cli_snapshot("reports_failing_assertion", &output);
}

#[test]
fn rejects_loops_without_invariants() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn bad_loop(mut x: i32) {
    loop {
        if x > 0 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
"#,
    );
    assert_cli_snapshot("rejects_loops_without_invariants", &output);
}

#[test]
fn abstracts_mutable_reference_calls() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

fn bump(x: &mut i32) -> i32 {
    *x += 1;
    *x
}

#[tsuno::verify]
fn bad_after_call(mut x: i32) {
    let r = &mut x;
    let _ = bump(r);
    tsuno::assert!(x == 0);
}

fn main() {}
"#,
    );
    assert_cli_snapshot("abstracts_mutable_reference_calls", &output);
}

#[test]
fn rejects_open_mutable_reference_after_abstract_call() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

fn opaque(_: &mut i32) {}

#[tsuno::verify]
fn bad_close(mut x: i32) {
    let r = &mut x;
    opaque(r);
}

fn main() {}
"#,
    );
    assert_cli_snapshot(
        "rejects_open_mutable_reference_after_abstract_call",
        &output,
    );
}

#[test]
fn allows_reestablishing_mutable_reference_after_abstract_call() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

fn opaque(_: &mut i32) {}

#[tsuno::verify]
fn close_ok(mut x: i32) {
    let r = &mut x;
    opaque(r);
    *r = 1;
}

fn main() {}
"#,
    );
    assert_cli_snapshot(
        "allows_reestablishing_mutable_reference_after_abstract_call",
        &output,
    );
}

#[test]
fn rejects_open_mutable_reference_on_storage_dead() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

fn opaque(_: &mut i32) {}

#[tsuno::verify]
fn bad_scope(mut x: i32) {
    {
        let r = &mut x;
        opaque(r);
    }
}

fn main() {}
"#,
    );
    assert_cli_snapshot("rejects_open_mutable_reference_on_storage_dead", &output);
}

#[test]
fn verifies_checked_integer_arithmetic() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn arithmetic() {
    let y = 1_i32 + 1_i32;
    tsuno::assert!(y == 2);
}

fn main() {}
"#,
    );
    assert_cli_snapshot("verifies_checked_integer_arithmetic", &output);
}

#[test]
fn verifies_loop_invariant_on_simple_loop() {
    let output = run_fixture(
        r#"#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn loop_ok() {
    let mut x = 0_i32;
    #[tsuno::invariant(x <= 10)]
    loop {
        if x >= 10 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
"#,
    );
    assert_cli_snapshot("verifies_loop_invariant_on_simple_loop", &output);
}
