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

use crate::engine::verify;
use crate::prepass::compute_program_prepass;
use crate::report::{VerificationResult, print_report};
use rustc_driver::{Callbacks, Compilation, run_compiler};
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
        let prepass = match compute_program_prepass(tcx) {
            Ok(prepass) => prepass,
            Err(errors) => {
                self.results.extend(errors);
                return Compilation::Stop;
            }
        };
        self.results.extend(verify(tcx, prepass));
        Compilation::Stop
    }
}
