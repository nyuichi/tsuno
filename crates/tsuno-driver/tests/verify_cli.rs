use std::fs;
use std::process::Command;

use tempfile::tempdir;

fn run_fixture(main_rs: &str) -> std::process::Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    fs::write(
        root.join("Cargo.toml"),
        r#"[package]
name = "fixture"
version = "0.1.0"
edition = "2024"

[dependencies]
tsuno = { path = "/Users/yuichi/tsuno/crates/tsuno" }
"#,
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
    assert!(
        output.status.success(),
        "status: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("ok"));
    assert!(stdout.contains("PASS"));
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
    assert!(
        !output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("FAIL"));
    assert!(stdout.contains("bad"));
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
    assert!(
        !output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("UNSUPPORTED"));
    assert!(stdout.contains("requires #[tsuno::invariant(..)]"));
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
    assert!(
        !output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("FAIL"));
    assert!(stdout.contains("bad_after_call"));
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
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("PASS"));
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
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("PASS"));
}
