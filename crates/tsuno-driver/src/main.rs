#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::env;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use anyhow::Context;
use rustc_driver::{Callbacks, Compilation, run_compiler};
use rustc_hir::ItemKind;
use rustc_middle::ty::TyCtxt;
use tsuno_driver::engine::{Verifier, default_z3};
use tsuno_driver::report::VerificationResult;

fn main() {
    if let Err(err) = run_wrapper() {
        eprintln!("{err:#}");
        std::process::exit(1);
    }
}

fn run_wrapper() -> anyhow::Result<()> {
    let mut args = env::args().collect::<Vec<_>>();
    // Cargo inserts the wrapped rustc path at argv[1]; rustc_driver consumes the rest.
    if args.len() > 1 {
        args.remove(1);
    }
    let report_path = env::var("TSUNO_REPORT_PATH").context("missing report path")?;
    let mut callbacks = VerifyCallbacks {
        report_path: PathBuf::from(report_path),
        done: false,
    };
    run_compiler(&args, &mut callbacks);
    Ok(())
}

struct VerifyCallbacks {
    report_path: PathBuf,
    done: bool,
}

impl Callbacks for VerifyCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        if self.done {
            return Compilation::Continue;
        }
        self.done = true;
        let report_path = self.report_path.clone();
        let _ = collect_results(tcx, &report_path);
        Compilation::Continue
    }
}

fn collect_results<'tcx>(tcx: TyCtxt<'tcx>, report_path: &Path) -> anyhow::Result<()> {
    default_z3();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if !matches!(item.kind, ItemKind::Fn { .. }) {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let body = tcx.optimized_mir(local_def_id.to_def_id());
        let verifier = Verifier::new(tcx, local_def_id, body);
        if !verifier.has_verify_marker() {
            continue;
        }
        let result = verifier.verify();
        append_result(report_path, &result)?;
    }
    Ok(())
}

fn append_result(path: &Path, result: &VerificationResult) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("create report dir {}", parent.display()))?;
    }
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .with_context(|| format!("open report {}", path.display()))?;
    serde_json::to_writer(&mut file, result).context("serialize verification result")?;
    file.write_all(b"\n")
        .context("terminate verification result line")?;
    Ok(())
}
