# `cargo tsuno`

`cargo tsuno` verifies Rust crates through Cargo. It runs `cargo check` with
`tsuno-driver` installed as `RUSTC_WORKSPACE_WRAPPER`, so the verification
target is the same crate graph that Cargo checks.

## Verify a Cargo Workspace

From a Rust workspace or package, run:

```sh
cargo tsuno
```

By default this checks the package or workspace members selected by Cargo for
`cargo check`. The usual package-selection flags supported by tsuno are:

```sh
cargo tsuno --workspace
cargo tsuno -p my-crate
cargo tsuno --package my-crate
cargo tsuno --manifest-path path/to/Cargo.toml
```

`--workspace` verifies all workspace members selected by Cargo. `-p` /
`--package` narrows verification to named packages. `--manifest-path` chooses
the Cargo manifest used as the entry point.

## Verify With External Specs

`cargo tsuno` can also be run from a separate proof repository that contains a
`tsuno.toml` file. This lets production sources remain unchanged.

```text
prod-repo/
  Cargo.toml
  src/lib.rs
  src/foo.rs

proof-repo/
  tsuno.toml
  specs/
    src/foo.rs.tsuno
```

`proof-repo/tsuno.toml`:

```toml
[subject]
root = "../prod-repo"

[spec]
root = "specs"

[cargo]
workspace = true
```

Then run:

```sh
cd proof-repo
cargo tsuno
```

If `subject.manifest_path` is omitted, tsuno uses
`subject.root/Cargo.toml`.

External spec files are matched by subject-relative path. For example:

```text
../prod-repo/src/foo.rs
  -> specs/src/foo.rs.tsuno
```

The external `.rs.tsuno` contents are treated as if they were wrapped in
`/*@ ... */` and inserted at the start of the corresponding Rust source file.

## Configuration Discovery

`cargo tsuno` resolves inputs in this order:

1. if `--config path/to/tsuno.toml` is passed, use that file
2. otherwise search the current directory and its parents for `tsuno.toml`
3. if no `tsuno.toml` is found, search the current directory and its parents for
   `Cargo.toml`

CLI flags override or supplement config values:

```sh
cargo tsuno --config proof/tsuno.toml
cargo tsuno --subject ../prod-repo --spec-root specs
cargo tsuno --workspace -p my-crate
```

When `--spec-root` is used from inside a Cargo workspace without `--subject`,
the Cargo workspace root is used as the subject root.
