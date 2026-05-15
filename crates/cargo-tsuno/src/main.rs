use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, bail};
use camino::Utf8PathBuf;
use clap::Parser;
use serde::Deserialize;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Cli {
    config_path: Option<PathBuf>,
    subject_root: Option<PathBuf>,
    spec_root: Option<PathBuf>,
    workspace: bool,
    packages: Vec<String>,
    manifest_path: Option<PathBuf>,
}

#[derive(Parser)]
#[command(name = "cargo-tsuno")]
struct RawCli {
    /// Path to tsuno.toml.
    #[arg(long = "config")]
    config_path: Option<PathBuf>,

    /// Root of the repository being verified.
    #[arg(long = "subject")]
    subject_root: Option<PathBuf>,

    /// Root of the external .rs.tsuno overlay.
    #[arg(long = "spec-root")]
    spec_root: Option<PathBuf>,

    /// Verify all workspace members.
    #[arg(long)]
    workspace: bool,

    /// Verify only the named package.
    #[arg(short = 'p', long = "package")]
    packages: Vec<String>,

    /// Path to Cargo.toml.
    #[arg(long)]
    manifest_path: Option<PathBuf>,
}

impl Cli {
    fn parse() -> Self {
        Self::try_parse_from(std::env::args_os()).unwrap_or_else(|err| err.exit())
    }

    fn try_parse_from<I, T>(args: I) -> Result<Self, clap::Error>
    where
        I: IntoIterator<Item = T>,
        T: Into<OsString>,
    {
        let mut args = args.into_iter().map(Into::into).collect::<Vec<OsString>>();
        if args.get(1).is_some_and(|arg| arg == OsStr::new("tsuno")) {
            args.remove(1);
        }
        let raw = RawCli::try_parse_from(args)?;
        Ok(Self {
            config_path: raw.config_path,
            subject_root: raw.subject_root,
            spec_root: raw.spec_root,
            workspace: raw.workspace,
            packages: raw.packages,
            manifest_path: raw.manifest_path,
        })
    }
}

fn main() {
    match try_main() {
        Ok(code) => std::process::exit(code),
        Err(err) => {
            eprintln!("{err:#}");
            std::process::exit(1);
        }
    }
}

fn try_main() -> anyhow::Result<i32> {
    let cli = Cli::parse();
    let config = InvocationConfig::resolve(&cli)?;
    let invocation = CargoInvocation::discover(&config)?;
    verify(&invocation, &config)
}

#[derive(Debug, Clone)]
struct CargoInvocation {
    manifest_path: Utf8PathBuf,
    workspace_root: Utf8PathBuf,
    subject_root: Option<Utf8PathBuf>,
    spec_root: Option<Utf8PathBuf>,
}

#[derive(Debug, Clone, Default, Deserialize)]
struct TsunoConfig {
    subject: Option<SubjectConfig>,
    spec: Option<SpecConfig>,
    cargo: Option<CargoConfig>,
}

#[derive(Debug, Clone, Deserialize)]
struct SubjectConfig {
    root: PathBuf,
    manifest_path: Option<PathBuf>,
}

#[derive(Debug, Clone, Deserialize)]
struct SpecConfig {
    root: PathBuf,
}

#[derive(Debug, Clone, Default, Deserialize)]
struct CargoConfig {
    workspace: Option<bool>,
    packages: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
struct InvocationConfig {
    manifest_path: PathBuf,
    subject_root: Option<PathBuf>,
    spec_root: Option<PathBuf>,
    workspace: bool,
    packages: Vec<String>,
}

impl InvocationConfig {
    fn resolve(cli: &Cli) -> anyhow::Result<Self> {
        let current_dir = std::env::current_dir().context("get current dir")?;
        let config_path = match &cli.config_path {
            Some(path) => Some(resolve_path(&current_dir, path)),
            None => find_tsuno_config_from_current_dir()?,
        };
        let file_config = match &config_path {
            Some(path) => {
                let text = std::fs::read_to_string(path)
                    .with_context(|| format!("read config `{}`", path.display()))?;
                toml::from_str::<TsunoConfig>(&text)
                    .with_context(|| format!("parse config `{}`", path.display()))?
            }
            None => TsunoConfig::default(),
        };
        let config_dir = config_path
            .as_deref()
            .and_then(Path::parent)
            .unwrap_or(&current_dir);

        let subject_root = cli
            .subject_root
            .as_ref()
            .map(|path| resolve_path(&current_dir, path))
            .or_else(|| {
                file_config
                    .subject
                    .as_ref()
                    .map(|subject| resolve_path(config_dir, &subject.root))
            });
        let manifest_path = cli
            .manifest_path
            .as_ref()
            .map(|path| resolve_path(&current_dir, path))
            .or_else(|| {
                file_config
                    .subject
                    .as_ref()
                    .and_then(|subject| subject.manifest_path.as_ref())
                    .map(|path| resolve_path(config_dir, path))
            })
            .or_else(|| subject_root.as_ref().map(|root| root.join("Cargo.toml")))
            .map(Ok)
            .unwrap_or_else(find_manifest_path_from_current_dir)?;
        let spec_root = cli
            .spec_root
            .as_ref()
            .map(|path| resolve_path(&current_dir, path))
            .or_else(|| {
                file_config
                    .spec
                    .as_ref()
                    .map(|spec| resolve_path(config_dir, &spec.root))
            });
        let workspace = cli.workspace
            || file_config
                .cargo
                .as_ref()
                .and_then(|cargo| cargo.workspace)
                .unwrap_or(false);
        let packages = if cli.packages.is_empty() {
            file_config
                .cargo
                .and_then(|cargo| cargo.packages)
                .unwrap_or_default()
        } else {
            cli.packages.clone()
        };

        Ok(Self {
            manifest_path: std::fs::canonicalize(manifest_path).context("resolve manifest path")?,
            subject_root: subject_root
                .map(|path| std::fs::canonicalize(path).context("resolve subject root"))
                .transpose()?,
            spec_root: spec_root
                .map(|path| std::fs::canonicalize(path).context("resolve spec root"))
                .transpose()?,
            workspace,
            packages,
        })
    }

    fn cargo_check_args(&self, manifest_path: &Utf8PathBuf) -> Vec<String> {
        let mut args = vec![
            "check".to_string(),
            "--offline".to_string(),
            "--quiet".to_string(),
            "--manifest-path".to_string(),
            manifest_path.to_string(),
        ];
        if self.workspace {
            args.push("--workspace".to_string());
        }
        for package in &self.packages {
            args.push("--package".to_string());
            args.push(package.clone());
        }
        args
    }
}

#[derive(Debug, Deserialize)]
struct Metadata {
    workspace_root: String,
}

impl CargoInvocation {
    fn discover(config: &InvocationConfig) -> anyhow::Result<Self> {
        let output = Command::new("cargo")
            .args([
                "metadata",
                "--offline",
                "--format-version",
                "1",
                "--no-deps",
                "--manifest-path",
            ])
            .arg(&config.manifest_path)
            .output()
            .context("run cargo metadata")?;
        if !output.status.success() {
            bail!(
                "cargo metadata failed:\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let metadata: Metadata =
            serde_json::from_slice(&output.stdout).context("parse cargo metadata")?;
        Ok(Self {
            manifest_path: Utf8PathBuf::from_path_buf(config.manifest_path.clone())
                .map_err(|path| anyhow::anyhow!("non utf8 manifest path: {}", path.display()))?,
            workspace_root: Utf8PathBuf::from(metadata.workspace_root),
            subject_root: config
                .subject_root
                .clone()
                .map(Utf8PathBuf::from_path_buf)
                .transpose()
                .map_err(|path| anyhow::anyhow!("non utf8 subject root: {}", path.display()))?,
            spec_root: config
                .spec_root
                .clone()
                .map(Utf8PathBuf::from_path_buf)
                .transpose()
                .map_err(|path| anyhow::anyhow!("non utf8 spec root: {}", path.display()))?,
        })
    }
}

fn verify(invocation: &CargoInvocation, config: &InvocationConfig) -> anyhow::Result<i32> {
    let wrapper_exe = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name(format!("tsuno-driver{}", std::env::consts::EXE_SUFFIX));
    verify_with_driver(invocation, config, wrapper_exe)
}

fn verify_with_driver(
    invocation: &CargoInvocation,
    config: &InvocationConfig,
    wrapper_exe: PathBuf,
) -> anyhow::Result<i32> {
    let cargo_check_args = config.cargo_check_args(&invocation.manifest_path);

    // Cargo drives compilation here so rustc can be wrapped and analyzed MIR can be collected.
    let mut command = Command::new("cargo");
    command
        .current_dir(&invocation.workspace_root)
        .args(cargo_check_args)
        .env("RUSTC_WORKSPACE_WRAPPER", wrapper_exe);
    if let Some(spec_root) = &invocation.spec_root {
        let subject_root = invocation
            .subject_root
            .as_ref()
            .unwrap_or(&invocation.workspace_root);
        command.env("TSUNO_SUBJECT_ROOT", subject_root);
        command.env("TSUNO_SPEC_ROOT", spec_root);
    }
    let status = command
        .spawn()
        .context("run cargo check")?
        .wait()
        .context("wait for cargo check")?;

    Ok(status.code().unwrap_or(1))
}

fn resolve_path(base: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_owned()
    } else {
        base.join(path)
    }
}

fn find_tsuno_config_from_current_dir() -> anyhow::Result<Option<PathBuf>> {
    let current_dir = std::env::current_dir().context("get current dir")?;
    for dir in current_dir.ancestors() {
        let config_path = dir.join("tsuno.toml");
        if config_path.is_file() {
            return Ok(Some(config_path));
        }
    }
    Ok(None)
}

fn find_manifest_path_from_current_dir() -> anyhow::Result<PathBuf> {
    let current_dir = std::env::current_dir().context("get current dir")?;
    for dir in current_dir.ancestors() {
        let manifest_path = dir.join("Cargo.toml");
        if manifest_path.is_file() {
            return Ok(manifest_path);
        }
    }
    bail!("could not find Cargo.toml in current directory or ancestors");
}

#[cfg(test)]
mod tests {
    use super::{
        CargoInvocation, Cli, InvocationConfig, find_manifest_path_from_current_dir,
        verify_with_driver,
    };
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::{Mutex, MutexGuard, OnceLock};

    use camino::Utf8PathBuf;
    use tempfile::tempdir;

    struct CurrentDirGuard {
        previous_dir: PathBuf,
        _lock: MutexGuard<'static, ()>,
    }

    impl CurrentDirGuard {
        fn set_to(path: &Path) -> Self {
            static CURRENT_DIR_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
            let lock = CURRENT_DIR_LOCK
                .get_or_init(|| Mutex::new(()))
                .lock()
                .expect("current dir lock");
            let previous_dir = std::env::current_dir().expect("current dir");
            std::env::set_current_dir(path).expect("set current dir");
            Self {
                previous_dir,
                _lock: lock,
            }
        }
    }

    impl Drop for CurrentDirGuard {
        fn drop(&mut self) {
            std::env::set_current_dir(&self.previous_dir).expect("restore current dir");
        }
    }

    #[test]
    fn parses_without_subcommand() {
        Cli::try_parse_from(["cargo-tsuno"]).expect("parse cli");
    }

    #[test]
    fn parses_cargo_subcommand_name() {
        let cli = Cli::try_parse_from(["cargo-tsuno", "tsuno", "--workspace"]).expect("parse cli");

        assert!(cli.workspace);
    }

    #[test]
    fn parses_workspace_package_and_manifest_path() {
        let cli = Cli::try_parse_from([
            "cargo-tsuno",
            "--workspace",
            "-p",
            "first-crate",
            "--package",
            "second-crate",
            "--manifest-path",
            "crates/demo/Cargo.toml",
        ])
        .expect("parse cli");

        assert!(cli.workspace);
        assert_eq!(cli.packages, ["first-crate", "second-crate"]);
        assert_eq!(
            cli.manifest_path.as_deref(),
            Some(Path::new("crates/demo/Cargo.toml"))
        );
    }

    #[test]
    fn parses_external_proof_options() {
        let cli = Cli::try_parse_from([
            "cargo-tsuno",
            "--config",
            "tsuno.toml",
            "--subject",
            "../prod",
            "--spec-root",
            "specs",
        ])
        .expect("parse cli");

        assert_eq!(cli.config_path.as_deref(), Some(Path::new("tsuno.toml")));
        assert_eq!(cli.subject_root.as_deref(), Some(Path::new("../prod")));
        assert_eq!(cli.spec_root.as_deref(), Some(Path::new("specs")));
    }

    #[test]
    fn builds_cargo_check_selection_args() {
        let config = InvocationConfig {
            manifest_path: PathBuf::from("/repo/Cargo.toml"),
            subject_root: None,
            spec_root: None,
            workspace: true,
            packages: vec!["first-crate".to_owned(), "second-crate".to_owned()],
        };

        assert_eq!(
            config.cargo_check_args(&Utf8PathBuf::from("/repo/Cargo.toml")),
            [
                "check",
                "--offline",
                "--quiet",
                "--manifest-path",
                "/repo/Cargo.toml",
                "--workspace",
                "--package",
                "first-crate",
                "--package",
                "second-crate",
            ]
        );
    }

    #[test]
    fn resolves_tsuno_config_from_current_dir() {
        let temp_dir = tempdir().expect("tempdir");
        let proof_root = temp_dir.path().join("proofs");
        let subject_root = temp_dir.path().join("prod");
        let nested_dir = proof_root.join("nested");
        let spec_root = proof_root.join("specs");
        fs::create_dir_all(&nested_dir).expect("create nested dir");
        fs::create_dir_all(&spec_root).expect("create specs dir");
        fs::create_dir_all(&subject_root).expect("create subject dir");
        fs::write(
            subject_root.join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .expect("write manifest");
        fs::write(
            proof_root.join("tsuno.toml"),
            "[subject]\nroot = \"../prod\"\n\n[spec]\nroot = \"specs\"\n\n[cargo]\nworkspace = true\npackages = [\"demo\"]\n",
        )
        .expect("write config");
        let _guard = CurrentDirGuard::set_to(&nested_dir);
        let cli = Cli::try_parse_from(["cargo-tsuno"]).expect("parse cli");

        let config = InvocationConfig::resolve(&cli).expect("resolve invocation");

        assert_eq!(
            config.manifest_path,
            fs::canonicalize(subject_root.join("Cargo.toml")).expect("canonical manifest")
        );
        assert_eq!(
            config.subject_root,
            Some(fs::canonicalize(subject_root).expect("canonical subject"))
        );
        assert_eq!(
            config.spec_root,
            Some(fs::canonicalize(spec_root).expect("canonical specs"))
        );
        assert!(config.workspace);
        assert_eq!(config.packages, ["demo"]);
    }

    #[test]
    fn verifies_subject_from_tsuno_config() {
        let temp_dir = tempdir().expect("tempdir");
        let proof_root = temp_dir.path().join("proofs");
        let subject_root = temp_dir.path().join("prod");
        let subject_src = subject_root.join("src");
        let spec_src = proof_root.join("specs").join("src");
        fs::create_dir_all(&subject_src).expect("create subject src");
        fs::create_dir_all(&spec_src).expect("create spec src");
        fs::write(
            subject_root.join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .expect("write manifest");
        fs::write(
            subject_src.join("lib.rs"),
            "pub fn external_specified(x: i32) {\n    let mut y = x;\n    while y < 3 {\n        y = y + 1;\n    }\n}\n",
        )
        .expect("write subject lib");
        fs::write(
            spec_src.join("lib.rs.tsuno"),
            "fn external_specified(x: i32) -> ()\n  req x == 0i32\n  ens true\n{\n  at loop #0 {\n    inv {x} <= {y} && {y} <= 3i32;\n  }\n}\n",
        )
        .expect("write external spec");
        fs::write(
            proof_root.join("tsuno.toml"),
            "[subject]\nroot = \"../prod\"\n\n[spec]\nroot = \"specs\"\n",
        )
        .expect("write config");
        let _guard = CurrentDirGuard::set_to(&proof_root);
        let cli = Cli::try_parse_from(["cargo-tsuno"]).expect("parse cli");
        let config = InvocationConfig::resolve(&cli).expect("resolve invocation");
        let invocation = CargoInvocation::discover(&config).expect("discover cargo invocation");

        let driver = build_tsuno_driver();

        let code = verify_with_driver(&invocation, &config, driver).expect("verify subject");

        assert_eq!(code, 0);
    }

    #[test]
    fn rejects_unrecognized_subcommand() {
        assert!(Cli::try_parse_from(["cargo-tsuno", "verify"]).is_err());
    }

    #[test]
    fn finds_manifest_in_current_dir_ancestor_chain() {
        let temp_dir = tempdir().expect("tempdir");
        let manifest_path = temp_dir.path().join("Cargo.toml");
        fs::write(
            &manifest_path,
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .expect("write manifest");
        let nested_dir = temp_dir.path().join("nested").join("deeper");
        fs::create_dir_all(&nested_dir).expect("create nested dir");
        let _guard = CurrentDirGuard::set_to(&nested_dir);

        let found_manifest_path = find_manifest_path_from_current_dir().expect("find manifest");

        assert_eq!(
            fs::canonicalize(found_manifest_path).expect("canonicalize found manifest"),
            fs::canonicalize(manifest_path).expect("canonicalize expected manifest")
        );
    }

    fn build_tsuno_driver() -> PathBuf {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let workspace_root = manifest_dir
            .parent()
            .and_then(Path::parent)
            .expect("workspace root");
        let status = Command::new("cargo")
            .current_dir(workspace_root)
            .args(["build", "-p", "tsuno-driver", "--bin", "tsuno-driver"])
            .status()
            .expect("build tsuno-driver");
        assert!(status.success(), "tsuno-driver build failed");
        workspace_root
            .join("target")
            .join("debug")
            .join(format!("tsuno-driver{}", std::env::consts::EXE_SUFFIX))
    }
}
