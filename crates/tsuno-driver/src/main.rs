#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

mod directive;
mod engine;
mod prepass;
mod report;
mod spec;

use std::env;

use crate::engine::Verifier;
use crate::report::{VerificationResult, print_report};
use rustc_driver::{Callbacks, Compilation, run_compiler};
use rustc_hir::ItemKind;
use rustc_middle::ty::TyCtxt;

fn main() {
    let mut args = env::args().collect::<Vec<_>>();
    // Cargo inserts the wrapped rustc path at argv[1]; rustc_driver consumes the rest.
    if args.len() > 1 {
        args.remove(1);
    }
    let mut callbacks = VerifyCallbacks {
        done: false,
        results: Vec::new(),
    };
    run_compiler(&args, &mut callbacks);
    let success = print_report(&callbacks.results);
    if !success {
        std::process::exit(1);
    }
}

struct VerifyCallbacks {
    done: bool,
    results: Vec<VerificationResult>,
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
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            if !matches!(item.kind, ItemKind::Fn { .. }) {
                continue;
            }
            let local_def_id = item.owner_id.def_id;
            let body = tcx
                .mir_drops_elaborated_and_const_checked(local_def_id)
                .steal();
            let verifier = Verifier::new(tcx, local_def_id, item.span, body);
            self.results.push(verifier.verify());
        }
        Compilation::Continue
    }
}
