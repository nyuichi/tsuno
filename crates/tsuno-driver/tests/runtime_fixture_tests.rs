use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::tempdir;

fn fixture_file(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/snapshots/pass")
        .join(format!("{name}.rs"))
}

fn compile_and_run_fixture(name: &str) -> Output {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path();
    fs::create_dir(root.join("src")).expect("src dir");
    fs::copy(fixture_file(name), root.join("src/fixture.rs")).expect("copy fixture");
    fs::write(
        root.join("src/main.rs"),
        r#"mod fixture {
    #![allow(dead_code)]
    include!("fixture.rs");

    pub fn exercise() {
        let mut swap_vec = vec![1, 2, 3, 4];
        assert_eq!(vec_len(&swap_vec), 4);
        vec_swap(&mut swap_vec, 1, 3);
        assert_eq!(swap_vec, vec![1, 4, 3, 2]);

        let mut rev_vec = vec![1, 2, 3, 4];
        rev(&mut rev_vec);
        assert_eq!(rev_vec, vec![4, 3, 2, 1]);
    }
}

fn main() {
    fixture::exercise();
}
"#,
    )
    .expect("write harness");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let binary = root.join("fixture-bin");
    let compile = Command::new(&rustc)
        .current_dir(root)
        .args([
            "--edition=2024",
            "src/main.rs",
            "-o",
            binary.to_str().expect("binary path"),
        ])
        .output()
        .expect("compile fixture");
    assert!(
        compile.status.success(),
        "fixture compilation failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&compile.stdout),
        String::from_utf8_lossy(&compile.stderr)
    );

    Command::new(binary).output().expect("run fixture")
}

#[test]
fn verifies_vec_reverse_fixture_runs_with_rust_bodies() {
    let output = compile_and_run_fixture("verifies_vec_reverse");
    assert!(
        output.status.success(),
        "fixture execution failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
