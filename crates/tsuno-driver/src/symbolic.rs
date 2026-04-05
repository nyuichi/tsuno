#![allow(clippy::result_large_err)]

use std::collections::{BTreeMap, BTreeSet, HashMap};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{
    BasicBlock, BinOp, Body, BorrowKind, ConstOperand, Local, Operand, Place, PlaceElem, Rvalue,
    Statement, StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::ty::{IntTy, TyCtxt, TyKind, UintTy};
use rustc_span::Span;
use rustc_span::source_map::Spanned;
use z3::ast::{Ast, Bool, Int};
use z3::{Config, Context as Z3Context, SatResult, Solver};

use crate::diagnostic::{VerificationResult, VerificationStatus};
use crate::loop_info::{LoopInfo, compute_loops};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Loc(pub usize);

#[derive(Debug, Clone)]
pub struct State<'ctx> {
    env: BTreeMap<Local, Loc>,
    store: BTreeMap<Loc, SymVal<'ctx>>,
    pc: Vec<Bool<'ctx>>,
    ctrl: ControlPoint,
    next_loc: usize,
    next_sym: usize,
    trace: Vec<String>,
    assumed_loops: BTreeSet<usize>,
}

#[derive(Debug, Clone, Copy)]
pub struct ControlPoint {
    basic_block: BasicBlock,
    statement_index: usize,
}

#[derive(Debug, Clone)]
pub enum SymVal<'ctx> {
    Scalar(TypedExpr<'ctx>),
    Pair(TypedExpr<'ctx>, TypedExpr<'ctx>),
    MutRef {
        target: Loc,
        cur: TypedExpr<'ctx>,
        fin: TypedExpr<'ctx>,
    },
}

#[derive(Debug, Clone)]
pub enum TypedExpr<'ctx> {
    Bool(Bool<'ctx>),
    Int(Int<'ctx>),
    Unit,
}

pub struct Verifier<'ctx, 'tcx> {
    z3: &'ctx Z3Context,
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'tcx Body<'tcx>,
    loops: HashMap<BasicBlock, LoopInfo>,
}

impl<'ctx, 'tcx> Verifier<'ctx, 'tcx> {
    pub fn new(
        z3: &'ctx Z3Context,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        body: &'tcx Body<'tcx>,
    ) -> Self {
        Self {
            z3,
            tcx,
            def_id,
            body,
            loops: compute_loops(body),
        }
    }

    pub fn has_verify_marker(&self) -> bool {
        self.body.basic_blocks.iter_enumerated().any(|(_, bb)| {
            matches!(
                &bb.terminator().kind,
                TerminatorKind::Call { func, .. } if self.is_marker(func, "__tsuno_verify")
            )
        })
    }

    pub fn verify(&self) -> VerificationResult {
        if let Some(result) = self.check_loop_annotations() {
            return result;
        }
        let mut queue = vec![self.initial_state()];
        while let Some(state) = queue.pop() {
            let data = &self.body.basic_blocks[state.ctrl.basic_block];
            if state.ctrl.statement_index < data.statements.len() {
                let stmt_index = state.ctrl.statement_index;
                match self.step_statement(state, &data.statements[stmt_index]) {
                    Ok(next) => queue.push(next),
                    Err(result) => return result,
                }
                continue;
            }
            match self.step_terminator(state, data.terminator()) {
                Ok(nexts) => queue.extend(nexts),
                Err(result) => return result,
            }
        }
        self.pass_result("all assertions discharged")
    }

    fn check_loop_annotations(&self) -> Option<VerificationResult> {
        for (header, loop_info) in &self.loops {
            let data = &self.body.basic_blocks[*header];
            let term = data.terminator();
            if !matches!(
                &term.kind,
                TerminatorKind::Call { func, .. } if self.is_marker(func, "__tsuno_invariant")
            ) {
                return Some(self.unsupported_result(
                    term.source_info.span,
                    Some(header.index()),
                    None,
                    format!(
                        "loop at bb{} requires #[tsuno::invariant(..)]",
                        loop_info.header.index()
                    ),
                    Vec::new(),
                ));
            }
        }
        None
    }

    fn step_statement(
        &self,
        mut state: State<'ctx>,
        stmt: &Statement<'tcx>,
    ) -> Result<State<'ctx>, VerificationResult> {
        state.trace.push(format!(
            "bb{}:stmt{}",
            state.ctrl.basic_block.index(),
            state.ctrl.statement_index
        ));
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                if !state.env.contains_key(local) {
                    let value = self.fresh_symval_for_ty(
                        &mut state,
                        self.body.local_decls[*local].ty,
                        &format!("live_{}", local.as_usize()),
                    )?;
                    let loc = state.alloc(value);
                    state.env.insert(*local, loc);
                }
            }
            StatementKind::StorageDead(local) => {
                self.close_local(&mut state, *local, stmt.source_info.span)?;
            }
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                self.assign(&mut state, *place, rvalue, stmt.source_info.span)?;
            }
            StatementKind::Nop
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. } => {}
            other => {
                return Err(self.unsupported_result(
                    stmt.source_info.span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("unsupported MIR statement {other:?}"),
                    state.trace,
                ));
            }
        }
        state.ctrl.statement_index += 1;
        Ok(state)
    }

    fn step_terminator(
        &self,
        state: State<'ctx>,
        term: &Terminator<'tcx>,
    ) -> Result<Vec<State<'ctx>>, VerificationResult> {
        let mut state = state;
        state
            .trace
            .push(format!("bb{}:term", state.ctrl.basic_block.index()));
        match &term.kind {
            TerminatorKind::Goto { target } => Ok(vec![state.goto(*target)]),
            TerminatorKind::Return => {
                self.close_live_mut_refs(&mut state, term.source_info.span)?;
                Ok(Vec::new())
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.step_switch(state, discr, targets, term.source_info.span)
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                msg,
                ..
            } => {
                let cond = self.scalar_from_operand(&state, cond, term.source_info.span)?;
                let formula = if *expected {
                    cond.as_bool(self.z3)?
                } else {
                    cond.as_bool(self.z3)?.not()
                };
                self.ensure_formula(
                    &state,
                    formula,
                    term.source_info.span,
                    format!("assertion failed: {msg:?}"),
                )?;
                Ok(vec![state.goto(*target)])
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => self.step_call(
                state,
                func,
                args,
                *destination,
                *target,
                term.source_info.span,
            ),
            other => Err(self.unsupported_result(
                term.source_info.span,
                Some(state.ctrl.basic_block.index()),
                None,
                format!("unsupported MIR terminator {other:?}"),
                state.trace,
            )),
        }
    }

    fn step_switch(
        &self,
        state: State<'ctx>,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        span: Span,
    ) -> Result<Vec<State<'ctx>>, VerificationResult> {
        let discr = self.scalar_from_operand(&state, discr, span)?;
        let mut explicit = Vec::new();
        let mut next_states = Vec::new();
        for (value, target) in targets.iter() {
            let cond = match &discr {
                TypedExpr::Bool(expr) => expr._eq(&Bool::from_bool(self.z3, value != 0)),
                TypedExpr::Int(expr) => expr._eq(&Int::from_i64(self.z3, value as i64)),
                TypedExpr::Unit => {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        None,
                        "switch on unit is unsupported".to_owned(),
                        state.trace,
                    ));
                }
            };
            explicit.push(cond.clone());
            let mut next = state.clone().goto(target);
            next.pc.push(cond);
            if self.path_is_feasible(&next) {
                next_states.push(next);
            }
        }
        let mut otherwise = state.goto(targets.otherwise());
        let negated: Vec<_> = explicit.iter().map(|cond| cond.not()).collect();
        otherwise.pc.push(if negated.is_empty() {
            Bool::from_bool(self.z3, true)
        } else {
            Bool::and(self.z3, &negated.iter().collect::<Vec<_>>())
        });
        if self.path_is_feasible(&otherwise) {
            next_states.push(otherwise);
        }
        Ok(next_states)
    }

    fn step_call(
        &self,
        mut state: State<'ctx>,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Span,
    ) -> Result<Vec<State<'ctx>>, VerificationResult> {
        if self.is_marker(func, "__tsuno_verify") {
            let target = target.expect("verify marker should return");
            return Ok(vec![state.goto(target)]);
        }
        if self.is_marker(func, "__tsuno_assert") {
            let cond = self.scalar_from_operand(&state, &args[0].node, span)?;
            self.ensure_formula(
                &state,
                cond.as_bool(self.z3)?,
                span,
                "tsuno assertion failed".to_owned(),
            )?;
            let target = target.expect("assert marker should return");
            return Ok(vec![state.goto(target)]);
        }
        if self.is_marker(func, "__tsuno_invariant") {
            let cond = self.scalar_from_operand(&state, &args[0].node, span)?;
            let header = state.ctrl.basic_block.index();
            self.ensure_formula(
                &state,
                cond.as_bool(self.z3)?,
                span,
                "loop invariant does not hold".to_owned(),
            )?;
            let target = target.expect("invariant marker should return");
            if let Some(loop_info) = self.loops.get(&state.ctrl.basic_block) {
                if state.assumed_loops.contains(&header) {
                    return Ok(Vec::new());
                }
                let mut next = state.goto(target);
                next.assumed_loops.insert(header);
                self.havoc_loop(&mut next, loop_info, span)?;
                let assumed = self.scalar_from_operand(&next, &args[0].node, span)?;
                next.pc.push(assumed.as_bool(self.z3)?);
                return Ok(vec![next]);
            }
            return Ok(vec![state.goto(target)]);
        }

        for arg in args {
            if let Operand::Copy(place) | Operand::Move(place) = arg.node
                && let Some((base_loc, target_loc)) = self.mut_ref_targets(&state, place)
            {
                let ty = self.place_ty(place);
                let target_ty = match ty.kind() {
                    TyKind::Ref(_, inner, _) => *inner,
                    _ => self.body.local_decls[place.local].ty,
                };
                let fresh = self.fresh_scalar_for_ty(&mut state, target_ty, "call_mut")?;
                let fin = match state.store.get(&base_loc).cloned() {
                    Some(SymVal::MutRef { fin, .. }) => fin,
                    _ => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            None,
                            "missing mutable reference argument".to_owned(),
                            state.trace.clone(),
                        ));
                    }
                };
                state.store.insert(
                    base_loc,
                    SymVal::MutRef {
                        target: target_loc,
                        cur: fresh.clone(),
                        fin,
                    },
                );
                state.store.insert(target_loc, SymVal::Scalar(fresh));
            }
        }
        let value = self.fresh_symval_for_ty(&mut state, self.place_ty(destination), "call_ret")?;
        self.write_place(&mut state, destination, value, span)?;
        let target = target.ok_or_else(|| {
            self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                None,
                "call without return target".to_owned(),
                state.trace.clone(),
            )
        })?;
        Ok(vec![state.goto(target)])
    }

    fn havoc_loop(
        &self,
        state: &mut State<'ctx>,
        loop_info: &LoopInfo,
        span: Span,
    ) -> Result<(), VerificationResult> {
        for local in &loop_info.written_locals {
            let Some(loc) = state.env.get(local).copied() else {
                continue;
            };
            let current = state.store.get(&loc).cloned();
            match current {
                Some(SymVal::Scalar(_)) | Some(SymVal::Pair(..)) => {
                    let value = self.fresh_symval_for_ty(
                        state,
                        self.body.local_decls[*local].ty,
                        "loop_havoc",
                    )?;
                    state.store.insert(loc, value);
                }
                Some(SymVal::MutRef { target, .. }) => {
                    let TyKind::Ref(_, inner, _) = self.body.local_decls[*local].ty.kind() else {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            None,
                            "unexpected mutable reference type".to_owned(),
                            state.trace.clone(),
                        ));
                    };
                    let fresh = self.fresh_scalar_for_ty(state, *inner, "loop_ref")?;
                    state.store.insert(
                        loc,
                        SymVal::MutRef {
                            target,
                            cur: fresh.clone(),
                            fin: fresh.clone(),
                        },
                    );
                    state.store.insert(target, SymVal::Scalar(fresh));
                }
                None => {}
            }
        }
        Ok(())
    }

    fn assign(
        &self,
        state: &mut State<'ctx>,
        place: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let value = match rvalue {
            Rvalue::Use(operand) => self.operand_to_symval(state, operand, span)?,
            Rvalue::BinaryOp(op, operands) => {
                let (lhs, rhs) = &**operands;
                self.binary_value(state, *op, lhs, rhs, span)?
            }
            Rvalue::UnaryOp(op, operand) => {
                SymVal::Scalar(self.unary_value(state, *op, operand, span)?)
            }
            Rvalue::Ref(_, borrow_kind, borrowed_place) => match borrow_kind {
                BorrowKind::Mut { .. } => {
                    let target = self.place_loc(state, *borrowed_place, span)?;
                    let scalar = self.scalar_from_place(state, *borrowed_place, span)?;
                    SymVal::MutRef {
                        target,
                        cur: scalar.clone(),
                        fin: scalar,
                    }
                }
                BorrowKind::Shared => {
                    SymVal::Scalar(self.scalar_from_place(state, *borrowed_place, span)?)
                }
                other => {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("unsupported borrow kind {other:?}"),
                        state.trace.clone(),
                    ));
                }
            },
            other => {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("unsupported MIR rvalue {other:?}"),
                    state.trace.clone(),
                ));
            }
        };
        self.write_place(state, place, value, span)
    }

    fn binary_value(
        &self,
        state: &State<'ctx>,
        op: BinOp,
        lhs_operand: &Operand<'tcx>,
        rhs_operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymVal<'ctx>, VerificationResult> {
        let lhs_ty = self.operand_ty(lhs_operand, span, state)?;
        let lhs = self.scalar_from_operand(state, lhs_operand, span)?;
        let rhs = self.scalar_from_operand(state, rhs_operand, span)?;
        let value = match op {
            BinOp::Add => {
                SymVal::Scalar(TypedExpr::Int(lhs.as_int(self.z3)? + rhs.as_int(self.z3)?))
            }
            BinOp::Sub => {
                SymVal::Scalar(TypedExpr::Int(lhs.as_int(self.z3)? - rhs.as_int(self.z3)?))
            }
            BinOp::Mul => {
                SymVal::Scalar(TypedExpr::Int(lhs.as_int(self.z3)? * rhs.as_int(self.z3)?))
            }
            BinOp::Eq => SymVal::Scalar(TypedExpr::Bool(lhs.eq(&rhs, self.z3)?)),
            BinOp::Ne => SymVal::Scalar(TypedExpr::Bool(lhs.eq(&rhs, self.z3)?.not())),
            BinOp::Gt => SymVal::Scalar(TypedExpr::Bool(
                lhs.as_int(self.z3)?.gt(&rhs.as_int(self.z3)?),
            )),
            BinOp::Ge => SymVal::Scalar(TypedExpr::Bool(
                lhs.as_int(self.z3)?.ge(&rhs.as_int(self.z3)?),
            )),
            BinOp::Lt => SymVal::Scalar(TypedExpr::Bool(
                lhs.as_int(self.z3)?.lt(&rhs.as_int(self.z3)?),
            )),
            BinOp::Le => SymVal::Scalar(TypedExpr::Bool(
                lhs.as_int(self.z3)?.le(&rhs.as_int(self.z3)?),
            )),
            BinOp::AddWithOverflow => {
                let result = lhs.as_int(self.z3)? + rhs.as_int(self.z3)?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                SymVal::Pair(TypedExpr::Int(result), TypedExpr::Bool(overflow))
            }
            BinOp::SubWithOverflow => {
                let result = lhs.as_int(self.z3)? - rhs.as_int(self.z3)?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                SymVal::Pair(TypedExpr::Int(result), TypedExpr::Bool(overflow))
            }
            BinOp::MulWithOverflow => {
                let result = lhs.as_int(self.z3)? * rhs.as_int(self.z3)?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                SymVal::Pair(TypedExpr::Int(result), TypedExpr::Bool(overflow))
            }
            other => {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("unsupported binary op {other:?}"),
                    state.trace.clone(),
                ));
            }
        };
        Ok(value)
    }

    fn unary_value(
        &self,
        state: &State<'ctx>,
        op: UnOp,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<TypedExpr<'ctx>, VerificationResult> {
        let value = self.scalar_from_operand(state, operand, span)?;
        match op {
            UnOp::Not => Ok(TypedExpr::Bool(value.as_bool(self.z3)?.not())),
            UnOp::Neg => Ok(TypedExpr::Int(-value.as_int(self.z3)?)),
            other => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                format!("unsupported unary op {other:?}"),
                state.trace.clone(),
            )),
        }
    }

    fn operand_to_symval(
        &self,
        state: &State<'ctx>,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymVal<'ctx>, VerificationResult> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.read_place(state, *place, span),
            Operand::Constant(constant) => self.constant_to_symval(constant, span),
        }
    }

    fn scalar_from_operand(
        &self,
        state: &State<'ctx>,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<TypedExpr<'ctx>, VerificationResult> {
        match self.operand_to_symval(state, operand, span)? {
            SymVal::Scalar(expr) => Ok(expr),
            SymVal::MutRef { cur, .. } => Ok(cur),
            SymVal::Pair(..) => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "tuple value used where scalar was expected".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn scalar_from_place(
        &self,
        state: &State<'ctx>,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<TypedExpr<'ctx>, VerificationResult> {
        match self.read_place(state, place, span)? {
            SymVal::Scalar(expr) => Ok(expr),
            SymVal::MutRef { cur, .. } => Ok(cur),
            SymVal::Pair(..) => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "tuple value used where scalar was expected".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn read_place(
        &self,
        state: &State<'ctx>,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymVal<'ctx>, VerificationResult> {
        if let Some(local) = place.as_local() {
            let loc = state.env.get(&local).copied().ok_or_else(|| {
                self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("missing env for local {}", local.as_usize()),
                    state.trace.clone(),
                )
            })?;
            return state.store.get(&loc).cloned().ok_or_else(|| {
                self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("missing store for local {}", local.as_usize()),
                    state.trace.clone(),
                )
            });
        }
        let Some((base, elem)) = place.as_ref().last_projection() else {
            return Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "unsupported place".to_owned(),
                state.trace.clone(),
            ));
        };
        match elem {
            PlaceElem::Deref => {
                let base_place = base.to_place(self.tcx);
                let loc = self.place_loc(state, base_place, span)?;
                let SymVal::MutRef { target, .. } =
                    state.store.get(&loc).cloned().ok_or_else(|| {
                        self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "missing mutable reference".to_owned(),
                            state.trace.clone(),
                        )
                    })?
                else {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "deref of non-mutable reference".to_owned(),
                        state.trace.clone(),
                    ));
                };
                state.store.get(&target).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "missing deref target".to_owned(),
                        state.trace.clone(),
                    )
                })
            }
            PlaceElem::Field(field, _) => {
                let base_place = base.to_place(self.tcx);
                match self.read_place(state, base_place, span)? {
                    SymVal::Pair(first, second) => match field.index() {
                        0 => Ok(SymVal::Scalar(first)),
                        1 => Ok(SymVal::Scalar(second)),
                        index => Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            format!("unsupported tuple field {index}"),
                            state.trace.clone(),
                        )),
                    },
                    other => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("field projection on unsupported value {other:?}"),
                        state.trace.clone(),
                    )),
                }
            }
            other => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                format!("unsupported place projection {other:?}"),
                state.trace.clone(),
            )),
        }
    }

    fn write_place(
        &self,
        state: &mut State<'ctx>,
        place: Place<'tcx>,
        value: SymVal<'ctx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        if let Some(local) = place.as_local() {
            let loc = if let Some(loc) = state.env.get(&local).copied() {
                loc
            } else {
                let loc = state.alloc(SymVal::Scalar(TypedExpr::Unit));
                state.env.insert(local, loc);
                loc
            };
            state.store.insert(loc, value);
            return Ok(());
        }
        let Some((base, elem)) = place.as_ref().last_projection() else {
            return Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "unsupported place write".to_owned(),
                state.trace.clone(),
            ));
        };
        match elem {
            PlaceElem::Deref => {
                let base_place = base.to_place(self.tcx);
                let base_loc = self.place_loc(state, base_place, span)?;
                let target = match state.store.get(&base_loc) {
                    Some(SymVal::MutRef { target, .. }) => *target,
                    _ => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "deref write through non-mutable reference".to_owned(),
                            state.trace.clone(),
                        ));
                    }
                };
                let SymVal::Scalar(expr) = value else {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "non-scalar write through deref".to_owned(),
                        state.trace.clone(),
                    ));
                };
                state.store.insert(
                    base_loc,
                    SymVal::MutRef {
                        target,
                        cur: expr.clone(),
                        fin: expr.clone(),
                    },
                );
                state.store.insert(target, SymVal::Scalar(expr));
                Ok(())
            }
            other => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                format!("unsupported write projection {other:?}"),
                state.trace.clone(),
            )),
        }
    }

    fn place_loc(
        &self,
        state: &State<'ctx>,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<Loc, VerificationResult> {
        if let Some(local) = place.as_local() {
            return state.env.get(&local).copied().ok_or_else(|| {
                self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("missing env for local {}", local.as_usize()),
                    state.trace.clone(),
                )
            });
        }
        let Some((base, PlaceElem::Deref)) = place.as_ref().last_projection() else {
            return Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "unsupported place loc".to_owned(),
                state.trace.clone(),
            ));
        };
        let base_place = base.to_place(self.tcx);
        let base_loc = self.place_loc(state, base_place, span)?;
        match state.store.get(&base_loc) {
            Some(SymVal::MutRef { target, .. }) => Ok(*target),
            _ => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "deref loc through non-mutable reference".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn mut_ref_targets(&self, state: &State<'ctx>, place: Place<'tcx>) -> Option<(Loc, Loc)> {
        let local = place.as_local()?;
        let base_loc = state.env.get(&local).copied()?;
        match state.store.get(&base_loc) {
            Some(SymVal::MutRef { target, .. }) => Some((base_loc, *target)),
            _ => None,
        }
    }

    fn constant_to_symval(
        &self,
        constant: &ConstOperand<'tcx>,
        span: Span,
    ) -> Result<SymVal<'ctx>, VerificationResult> {
        let ty = constant.const_.ty();
        match ty.kind() {
            TyKind::Bool => {
                let value = constant.const_.try_to_bool().unwrap_or(false);
                Ok(SymVal::Scalar(TypedExpr::Bool(Bool::from_bool(
                    self.z3, value,
                ))))
            }
            TyKind::Int(_) | TyKind::Uint(_) => {
                let scalar = constant.const_.try_to_scalar_int().ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        None,
                        None,
                        "failed to evaluate integer constant".to_owned(),
                        Vec::new(),
                    )
                })?;
                let expr = if matches!(ty.kind(), TyKind::Int(_)) {
                    Int::from_i64(self.z3, scalar.to_int(scalar.size()) as i64)
                } else {
                    Int::from_u64(self.z3, scalar.to_uint(scalar.size()) as u64)
                };
                Ok(SymVal::Scalar(TypedExpr::Int(expr)))
            }
            TyKind::Tuple(fields) if fields.is_empty() => Ok(SymVal::Scalar(TypedExpr::Unit)),
            TyKind::FnDef(..) => Err(self.unsupported_result(
                span,
                None,
                None,
                "function constants are only supported in call position".to_owned(),
                Vec::new(),
            )),
            other => Err(self.unsupported_result(
                span,
                None,
                None,
                format!("unsupported constant type {other:?}"),
                Vec::new(),
            )),
        }
    }

    fn fresh_symval_for_ty(
        &self,
        state: &mut State<'ctx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        prefix: &str,
    ) -> Result<SymVal<'ctx>, VerificationResult> {
        match ty.kind() {
            TyKind::Bool => Ok(SymVal::Scalar(TypedExpr::Bool(
                self.fresh_bool(state, prefix),
            ))),
            TyKind::Int(_) | TyKind::Uint(_) => {
                let expr = self.fresh_int(state, prefix);
                if let Some(bounds) = int_range_constraint(self.z3, &expr, self.tcx, ty) {
                    state.pc.push(bounds);
                }
                Ok(SymVal::Scalar(TypedExpr::Int(expr)))
            }
            TyKind::Tuple(fields) if fields.is_empty() => Ok(SymVal::Scalar(TypedExpr::Unit)),
            TyKind::Tuple(fields)
                if fields.len() == 2 && matches!(fields[1].kind(), TyKind::Bool) =>
            {
                let first = self.fresh_symval_for_ty(state, fields[0], prefix)?;
                let SymVal::Scalar(first) = first else {
                    unreachable!();
                };
                Ok(SymVal::Pair(
                    first,
                    TypedExpr::Bool(self.fresh_bool(state, prefix)),
                ))
            }
            TyKind::Ref(_, inner, rustc_middle::mir::Mutability::Mut) => {
                let target_value = self.fresh_symval_for_ty(state, *inner, prefix)?;
                let SymVal::Scalar(target_scalar) = target_value else {
                    return Err(self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        None,
                        None,
                        "mutable references to non-scalars are unsupported".to_owned(),
                        Vec::new(),
                    ));
                };
                let target = state.alloc(SymVal::Scalar(target_scalar.clone()));
                Ok(SymVal::MutRef {
                    target,
                    cur: target_scalar.clone(),
                    fin: target_scalar,
                })
            }
            other => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                None,
                None,
                format!("unsupported type {other:?}"),
                Vec::new(),
            )),
        }
    }

    fn fresh_scalar_for_ty(
        &self,
        state: &mut State<'ctx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        prefix: &str,
    ) -> Result<TypedExpr<'ctx>, VerificationResult> {
        match self.fresh_symval_for_ty(state, ty, prefix)? {
            SymVal::Scalar(expr) => Ok(expr),
            _ => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                None,
                None,
                "expected scalar type".to_owned(),
                Vec::new(),
            )),
        }
    }

    fn fresh_bool(&self, state: &mut State<'ctx>, prefix: &str) -> Bool<'ctx> {
        let name = format!("{prefix}_{}", state.next_sym);
        state.next_sym += 1;
        Bool::new_const(self.z3, name)
    }

    fn fresh_int(&self, state: &mut State<'ctx>, prefix: &str) -> Int<'ctx> {
        let name = format!("{prefix}_{}", state.next_sym);
        state.next_sym += 1;
        Int::new_const(self.z3, name)
    }

    fn path_is_feasible(&self, state: &State<'ctx>) -> bool {
        let solver = Solver::new(self.z3);
        for cond in &state.pc {
            solver.assert(cond);
        }
        matches!(solver.check(), SatResult::Sat | SatResult::Unknown)
    }

    fn ensure_formula(
        &self,
        state: &State<'ctx>,
        formula: Bool<'ctx>,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let solver = Solver::new(self.z3);
        for cond in &state.pc {
            solver.assert(cond);
        }
        solver.assert(&formula.not());
        if solver.check() == SatResult::Sat {
            let model = solver
                .get_model()
                .map(|model| vec![("model".to_owned(), model.to_string())])
                .unwrap_or_default();
            return Err(VerificationResult {
                function: self.tcx.def_path_str(self.def_id.to_def_id()),
                status: VerificationStatus::Fail,
                span: span_text(self.tcx, span),
                basic_block: Some(state.ctrl.basic_block.index()),
                statement_index: Some(state.ctrl.statement_index),
                message,
                trace: state.trace.clone(),
                model,
            });
        }
        Ok(())
    }

    fn is_marker(&self, operand: &Operand<'tcx>, suffix: &str) -> bool {
        let Some(def_id) = call_target_def_id(operand) else {
            return false;
        };
        self.tcx.def_path_str(def_id).contains(suffix)
    }

    fn place_ty(&self, place: Place<'tcx>) -> rustc_middle::ty::Ty<'tcx> {
        place.ty(self.body, self.tcx).ty
    }

    fn operand_ty(
        &self,
        operand: &Operand<'tcx>,
        span: Span,
        state: &State<'ctx>,
    ) -> Result<rustc_middle::ty::Ty<'tcx>, VerificationResult> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => Ok(self.place_ty(*place)),
            Operand::Constant(constant) => {
                let ty = constant.const_.ty();
                match ty.kind() {
                    TyKind::Int(_) | TyKind::Uint(_) => Ok(ty),
                    _ => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("unsupported operand type for arithmetic {:?}", ty.kind()),
                        state.trace.clone(),
                    )),
                }
            }
        }
    }

    fn overflow_formula(
        &self,
        result: &Int<'ctx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        span: Span,
        state: &State<'ctx>,
    ) -> Result<Bool<'ctx>, VerificationResult> {
        match int_bounds(self.tcx, ty) {
            Some(IntBounds::Signed { min, max }) => {
                let low = result.lt(&Int::from_i64(self.z3, min));
                let high = result.gt(&Int::from_i64(self.z3, max));
                Ok(Bool::or(self.z3, &[&low, &high]))
            }
            Some(IntBounds::Unsigned { max }) => {
                let low = result.lt(&Int::from_i64(self.z3, 0));
                let high = result.gt(&Int::from_u64(self.z3, max));
                Ok(Bool::or(self.z3, &[&low, &high]))
            }
            None => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                format!("unsupported integer type {:?}", ty.kind()),
                state.trace.clone(),
            )),
        }
    }

    fn unsupported_result(
        &self,
        span: Span,
        basic_block: Option<usize>,
        statement_index: Option<usize>,
        message: String,
        trace: Vec<String>,
    ) -> VerificationResult {
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: VerificationStatus::Unsupported,
            span: span_text(self.tcx, span),
            basic_block,
            statement_index,
            message,
            trace,
            model: Vec::new(),
        }
    }

    fn pass_result(&self, message: &str) -> VerificationResult {
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: VerificationStatus::Pass,
            span: span_text(self.tcx, self.tcx.def_span(self.def_id)),
            basic_block: None,
            statement_index: None,
            message: message.to_owned(),
            trace: Vec::new(),
            model: Vec::new(),
        }
    }

    fn initial_state(&self) -> State<'ctx> {
        let mut state = State::empty();
        for local in std::iter::once(Local::from_usize(0)).chain(self.body.args_iter()) {
            let ty = self.body.local_decls[local].ty;
            let value = self
                .fresh_symval_for_ty(&mut state, ty, &format!("arg_{}", local.as_usize()))
                .expect("initial locals should be supported");
            let loc = state.alloc(value);
            state.env.insert(local, loc);
        }
        state
    }

    fn close_live_mut_refs(
        &self,
        state: &mut State<'ctx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let return_local = Local::from_usize(0);
        let locals: Vec<_> = state
            .env
            .iter()
            .filter_map(|(local, loc)| match state.store.get(loc) {
                Some(SymVal::MutRef { .. }) if *local != return_local => Some(*local),
                _ => None,
            })
            .collect();
        for local in locals {
            self.close_local(state, local, span)?;
        }
        Ok(())
    }

    fn close_local(
        &self,
        state: &mut State<'ctx>,
        local: Local,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let Some(loc) = state.env.remove(&local) else {
            return Ok(());
        };
        let Some(value) = state.store.remove(&loc) else {
            return Ok(());
        };
        let SymVal::MutRef { target, cur, fin } = value else {
            return Ok(());
        };
        self.ensure_formula(
            state,
            cur.eq(&fin, self.z3)?,
            span,
            "mutable reference close failed".to_owned(),
        )?;
        state.store.insert(target, SymVal::Scalar(cur));
        Ok(())
    }
}

impl<'ctx> State<'ctx> {
    fn empty() -> Self {
        Self {
            env: BTreeMap::new(),
            store: BTreeMap::new(),
            pc: Vec::new(),
            ctrl: ControlPoint {
                basic_block: BasicBlock::from_usize(0),
                statement_index: 0,
            },
            next_loc: 0,
            next_sym: 0,
            trace: Vec::new(),
            assumed_loops: BTreeSet::new(),
        }
    }

    fn alloc(&mut self, value: SymVal<'ctx>) -> Loc {
        let loc = Loc(self.next_loc);
        self.next_loc += 1;
        self.store.insert(loc, value);
        loc
    }

    fn goto(mut self, target: BasicBlock) -> Self {
        self.ctrl = ControlPoint {
            basic_block: target,
            statement_index: 0,
        };
        self
    }
}

impl<'ctx> TypedExpr<'ctx> {
    fn as_bool(&self, z3: &'ctx Z3Context) -> Result<Bool<'ctx>, VerificationResult> {
        match self {
            TypedExpr::Bool(expr) => Ok(expr.clone()),
            TypedExpr::Unit => Ok(Bool::from_bool(z3, true)),
            TypedExpr::Int(_) => Err(VerificationResult {
                function: String::new(),
                status: VerificationStatus::Unsupported,
                span: String::new(),
                basic_block: None,
                statement_index: None,
                message: "expected boolean expression".to_owned(),
                trace: Vec::new(),
                model: Vec::new(),
            }),
        }
    }

    fn as_int(&self, _z3: &'ctx Z3Context) -> Result<Int<'ctx>, VerificationResult> {
        match self {
            TypedExpr::Int(expr) => Ok(expr.clone()),
            _ => Err(VerificationResult {
                function: String::new(),
                status: VerificationStatus::Unsupported,
                span: String::new(),
                basic_block: None,
                statement_index: None,
                message: "expected integer expression".to_owned(),
                trace: Vec::new(),
                model: Vec::new(),
            }),
        }
    }

    fn eq(&self, rhs: &Self, z3: &'ctx Z3Context) -> Result<Bool<'ctx>, VerificationResult> {
        match (self, rhs) {
            (TypedExpr::Bool(lhs), TypedExpr::Bool(rhs)) => Ok(lhs._eq(rhs)),
            (TypedExpr::Int(lhs), TypedExpr::Int(rhs)) => Ok(lhs._eq(rhs)),
            (TypedExpr::Unit, TypedExpr::Unit) => Ok(Bool::from_bool(z3, true)),
            _ => Err(VerificationResult {
                function: String::new(),
                status: VerificationStatus::Unsupported,
                span: String::new(),
                basic_block: None,
                statement_index: None,
                message: "incompatible equality operands".to_owned(),
                trace: Vec::new(),
                model: Vec::new(),
            }),
        }
    }
}

fn call_target_def_id<'tcx>(operand: &Operand<'tcx>) -> Option<rustc_span::def_id::DefId> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

fn span_text(tcx: TyCtxt<'_>, span: Span) -> String {
    tcx.sess.source_map().span_to_diagnostic_string(span)
}

pub fn default_z3() -> Config {
    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    cfg
}

enum IntBounds {
    Signed { min: i64, max: i64 },
    Unsigned { max: u64 },
}

fn int_bounds(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> Option<IntBounds> {
    match ty.kind() {
        TyKind::Int(int_ty) => {
            let bits = match int_ty {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => return None,
                IntTy::Isize => tcx.data_layout.pointer_size().bits(),
            };
            let max = if bits == 64 {
                i64::MAX
            } else {
                (1_i64 << (bits - 1)) - 1
            };
            let min = if bits == 64 {
                i64::MIN
            } else {
                -(1_i64 << (bits - 1))
            };
            Some(IntBounds::Signed { min, max })
        }
        TyKind::Uint(uint_ty) => {
            let bits = match uint_ty {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => return None,
                UintTy::Usize => tcx.data_layout.pointer_size().bits(),
            };
            let max = if bits == 64 {
                u64::MAX
            } else {
                (1_u64 << bits) - 1
            };
            Some(IntBounds::Unsigned { max })
        }
        _ => None,
    }
}

fn int_range_constraint<'ctx>(
    z3: &'ctx Z3Context,
    expr: &Int<'ctx>,
    tcx: TyCtxt<'_>,
    ty: rustc_middle::ty::Ty<'_>,
) -> Option<Bool<'ctx>> {
    match int_bounds(tcx, ty)? {
        IntBounds::Signed { min, max } => {
            let low = expr.ge(&Int::from_i64(z3, min));
            let high = expr.le(&Int::from_i64(z3, max));
            Some(Bool::and(z3, &[&low, &high]))
        }
        IntBounds::Unsigned { max } => {
            let low = expr.ge(&Int::from_i64(z3, 0));
            let high = expr.le(&Int::from_u64(z3, max));
            Some(Bool::and(z3, &[&low, &high]))
        }
    }
}
