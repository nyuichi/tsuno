#![allow(clippy::result_large_err)]

use std::marker::PhantomData;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;

use crate::report::VerificationResult;

pub struct Verifier<'tcx>(PhantomData<&'tcx ()>);

impl<'tcx> Verifier<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId, body: Body<'tcx>) -> Self {
        let _ = (tcx, def_id, body);
        Self(PhantomData)
    }

    pub fn verify(&self) -> VerificationResult {
        panic!()
    }
}
