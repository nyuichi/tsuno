use std::env;
use std::path::{Path, PathBuf};

use anyhow::Context;
use rustc_driver::{Callbacks, Compilation, run_compiler};
use rustc_hir::ItemKind;
use rustc_middle::ty::TyCtxt;

use crate::report::append_result;
use crate::symbolic::{Verifier, default_z3};

pub const WRAPPER_ENV: &str = "TSUNO_WRAPPER_MODE";
pub const REPORT_PATH_ENV: &str = "TSUNO_REPORT_PATH";

pub fn maybe_run_wrapper() -> anyhow::Result<Option<i32>> {
    if env::var_os(WRAPPER_ENV).is_none() {
        return Ok(None);
    }
    let mut args = env::args().collect::<Vec<_>>();
    if args.len() > 1 {
        args.remove(1);
    }
    let report_path = env::var(REPORT_PATH_ENV).context("missing report path")?;
    let mut callbacks = VerifyCallbacks {
        report_path: PathBuf::from(report_path),
        done: false,
    };
    run_compiler(&args, &mut callbacks);
    Ok(Some(0))
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
    let cfg = default_z3();
    let z3 = z3::Context::new(&cfg);
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if !matches!(item.kind, ItemKind::Fn { .. }) {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let body = tcx.optimized_mir(local_def_id.to_def_id());
        let verifier = Verifier::new(&z3, tcx, local_def_id, body);
        if !verifier.has_verify_marker() {
            continue;
        }
        let result = verifier.verify();
        append_result(report_path, &result)?;
    }
    Ok(())
}
