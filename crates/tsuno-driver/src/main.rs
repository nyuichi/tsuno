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
use crate::prepass::{compute_function_prepass, compute_global_ghost_prepass};
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
        let ghosts = match compute_global_ghost_prepass(tcx) {
            Ok(ghosts) => ghosts,
            Err(error) => {
                self.results.push(VerificationResult {
                    function: "prepass".to_owned(),
                    status: crate::report::VerificationStatus::Unsupported,
                    span: error.display_span.unwrap_or_else(|| {
                        tcx.sess.source_map().span_to_diagnostic_string(error.span)
                    }),
                    message: error.message,
                });
                return Compilation::Stop;
            }
        };
        let mut items = Vec::new();
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            if !matches!(item.kind, ItemKind::Fn { .. }) {
                continue;
            }
            items.push((item.owner_id.def_id, item.span));
        }
        let Some((first_def_id, _first_span)) = items.first().copied() else {
            return Compilation::Stop;
        };
        let mut prepasses = Vec::with_capacity(items.len());
        let mut contracts = std::collections::HashMap::with_capacity(items.len());
        for (def_id, span) in &items {
            let body = tcx.mir_drops_elaborated_and_const_checked(*def_id);
            let prepass =
                match compute_function_prepass(tcx, *def_id, *span, &body.borrow(), &ghosts) {
                    Ok(prepass) => prepass,
                    Err(error) => {
                        self.results.push(error);
                        return Compilation::Stop;
                    }
                };
            let contract = prepass
                .function_contract
                .clone()
                .expect("successful function prepass must yield contract");
            contracts.insert(*def_id, contract);
            prepasses.push(prepass);
        }
        let first_body = tcx
            .mir_drops_elaborated_and_const_checked(first_def_id)
            .steal();
        let mut verifier = Verifier::new(tcx, first_def_id, first_body.clone(), contracts);
        for pure_fn in &ghosts.typed_pure_fns {
            if let Err(error) = verifier.load_ghost_function(pure_fn) {
                self.results.push(VerificationResult {
                    function: "prepass".to_owned(),
                    ..error
                });
                return Compilation::Stop;
            }
        }
        for lemma in &ghosts.typed_lemmas {
            if let Err(error) = verifier.load_ghost_lemma(lemma) {
                self.results.push(VerificationResult {
                    function: "prepass".to_owned(),
                    ..error
                });
                return Compilation::Stop;
            }
        }
        let mut prepass_iter = prepasses.into_iter();
        let first_prepass = prepass_iter
            .next()
            .expect("non-empty function list must yield first prepass");
        self.results
            .push(verifier.verify_function(first_def_id, first_body, first_prepass));
        for ((local_def_id, _span), prepass) in items.into_iter().skip(1).zip(prepass_iter) {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(local_def_id)
                .steal();
            self.results
                .push(verifier.verify_function(local_def_id, body, prepass));
        }
        Compilation::Stop
    }
}
