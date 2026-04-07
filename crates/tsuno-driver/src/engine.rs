#![allow(clippy::result_large_err)]

use std::cell::Cell;
use std::collections::{BTreeMap, HashMap, VecDeque};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{
    BasicBlock, BinOp, Body, BorrowKind, ConstOperand, Local, Operand, Place, PlaceElem, Rvalue,
    Statement, StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::ty::{IntTy, TyCtxt, TyKind, UintTy};
use rustc_span::Span;
use rustc_span::source_map::Spanned;
use z3::ast::{Bool, Int};
use z3::{SatResult, Solver, set_global_param};

use crate::prepass::{
    AssertionContracts, LoopContract, LoopContracts, MirSpecExpr, SwitchJoin, compute_assertions,
    compute_loops, compute_switch_joins,
};
use crate::report::{VerificationResult, VerificationStatus};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Loc(pub usize);

#[derive(Debug, Clone)]
pub struct State {
    env: BTreeMap<Local, Loc>,
    store: BTreeMap<Loc, SymVal>,
    pc: Vec<Bool>,
    ctrl: ControlPoint,
    trace: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ControlPoint {
    basic_block: BasicBlock,
    statement_index: usize,
}

#[derive(Debug, Clone)]
pub enum SymVal {
    Scalar(TypedExpr),
    Pair(TypedExpr, TypedExpr),
    MutRef {
        target: Loc,
        cur: TypedExpr,
        fin: TypedExpr,
    },
}

#[derive(Debug, Clone)]
pub enum TypedExpr {
    Bool(Bool),
    Int(Int),
    Unit,
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: Body<'tcx>,
    loop_contracts: LoopContracts,
    assertion_contracts: AssertionContracts,
    prepass_error: Option<VerificationResult>,
    switch_joins: HashMap<BasicBlock, SwitchJoin>,
    next_loc: Cell<usize>,
    next_sym: Cell<usize>,
}

impl<'tcx> Verifier<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId, body: Body<'tcx>) -> Self {
        let (loop_contracts, mut prepass_error) = match compute_loops(tcx, def_id, &body) {
            Ok(loop_contracts) => (loop_contracts, None),
            Err(error) => (
                LoopContracts::empty(),
                Some(VerificationResult {
                    function: tcx.def_path_str(def_id.to_def_id()),
                    status: VerificationStatus::Unsupported,
                    span: span_text(tcx, error.span),
                    basic_block: error.basic_block.map(|bb| bb.index()),
                    statement_index: error.statement_index,
                    message: error.message,
                    trace: Vec::new(),
                    model: Vec::new(),
                }),
            ),
        };
        let assertion_contracts = if prepass_error.is_none() {
            match compute_assertions(tcx, def_id, &body) {
                Ok(assertion_contracts) => assertion_contracts,
                Err(error) => {
                    prepass_error = Some(VerificationResult {
                        function: tcx.def_path_str(def_id.to_def_id()),
                        status: VerificationStatus::Unsupported,
                        span: span_text(tcx, error.span),
                        basic_block: error.basic_block.map(|bb| bb.index()),
                        statement_index: error.statement_index,
                        message: error.message,
                        trace: Vec::new(),
                        model: Vec::new(),
                    });
                    AssertionContracts::empty()
                }
            }
        } else {
            AssertionContracts::empty()
        };
        let switch_joins = compute_switch_joins(&body);
        Self {
            tcx,
            def_id,
            body,
            loop_contracts,
            assertion_contracts,
            prepass_error,
            switch_joins,
            next_loc: Cell::new(0),
            next_sym: Cell::new(0),
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
        if let Some(result) = self.prepass_error.clone() {
            return result;
        }
        let mut pending: BTreeMap<ControlPoint, Vec<State>> = BTreeMap::new();
        let mut worklist = VecDeque::new();
        self.enqueue_state(&mut pending, &mut worklist, self.initial_state());
        while let Some(ctrl) = worklist.pop_front() {
            let Some(mut bucket) = pending.remove(&ctrl) else {
                continue;
            };
            if ctrl.statement_index == 0
                && self.switch_joins.contains_key(&ctrl.basic_block)
                && bucket.len() > 1
            {
                let first = bucket[0].clone();
                assert!(
                    bucket.iter().skip(1).all(|state| state.ctrl == first.ctrl),
                    "join bucket control-point mismatch at bb{}",
                    ctrl.basic_block.index()
                );

                let mut common_len = 0;
                'outer: for idx in 0..first.pc.len() {
                    for state in &bucket[1..] {
                        assert!(
                            idx < state.pc.len(),
                            "join bucket path-condition mismatch at bb{}",
                            ctrl.basic_block.index()
                        );
                        if state.pc[idx].to_string() != first.pc[idx].to_string() {
                            break 'outer;
                        }
                    }
                    common_len += 1;
                }

                let mut merged = first.clone();
                merged.pc = first.pc[..common_len].to_vec();
                merged.env.clear();
                merged.store.clear();
                for state in &bucket {
                    let guard = state.pc.get(common_len).cloned().expect(
                        "join bucket must have a branch guard at the first divergent pc element",
                    );
                    for cond in &state.pc[common_len + 1..] {
                        merged.pc.push(guard.implies(cond));
                    }
                    merged.trace = common_prefix(&merged.trace, &state.trace);
                }

                let shared_locals: Vec<_> = first
                    .env
                    .keys()
                    .copied()
                    .filter(|local| {
                        bucket[1..]
                            .iter()
                            .all(|state| state.env.contains_key(local))
                    })
                    .collect();
                for local in shared_locals {
                    let first_loc = first
                        .env
                        .get(&local)
                        .copied()
                        .expect("shared local missing from first branch");
                    let mut merged_value = first
                        .store
                        .get(&first_loc)
                        .cloned()
                        .expect("shared local missing from first branch store");
                    for state in &bucket[1..] {
                        let guard = state.pc.get(common_len).cloned().expect(
                            "join bucket must have a branch guard at the first divergent pc element",
                        );
                        let incoming_loc = state
                            .env
                            .get(&local)
                            .copied()
                            .expect("shared local missing from incoming branch");
                        let incoming_value = state
                            .store
                            .get(&incoming_loc)
                            .cloned()
                            .expect("shared local missing from incoming branch store");
                        merged_value = self
                            .merge_symval(&guard, &merged_value, &incoming_value)
                            .expect("join bucket value shape mismatch");
                    }
                    let loc = self.alloc(&mut merged, merged_value);
                    merged.env.insert(local, loc);
                }
                bucket = vec![merged];
            }
            while let Some(state) = bucket.pop() {
                let data = &self.body.basic_blocks[state.ctrl.basic_block];
                if state.ctrl.statement_index < data.statements.len() {
                    let stmt_index = state.ctrl.statement_index;
                    match self.step_statement(state, &data.statements[stmt_index]) {
                        Ok(next) => self.enqueue_state(&mut pending, &mut worklist, next),
                        Err(result) => return result,
                    }
                    continue;
                }
                match self.step_terminator(state, data.terminator()) {
                    Ok(nexts) => {
                        for next in nexts {
                            self.enqueue_state(&mut pending, &mut worklist, next);
                        }
                    }
                    Err(result) => return result,
                }
            }
        }
        self.pass_result("all assertions discharged")
    }

    fn step_statement(
        &self,
        mut state: State,
        stmt: &Statement<'tcx>,
    ) -> Result<State, VerificationResult> {
        state.trace.push(format!(
            "bb{}:stmt{}",
            state.ctrl.basic_block.index(),
            state.ctrl.statement_index
        ));
        if let Some(assertion) = self
            .assertion_contracts
            .assertion_at(state.ctrl.basic_block, state.ctrl.statement_index)
        {
            let formula =
                self.spec_expr_to_bool(&state, &assertion.assertion, stmt.source_info.span)?;
            self.ensure_formula(
                &state,
                formula,
                assertion.assertion_span,
                "assertion failed".to_owned(),
            )?;
        }
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                let value = self.fresh_symval_for_ty(
                    &mut state,
                    self.body.local_decls[*local].ty,
                    &format!("live_{}", local.as_usize()),
                )?;
                let loc = self.alloc(&mut state, value);
                state.env.insert(*local, loc);
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
        state: State,
        term: &Terminator<'tcx>,
    ) -> Result<Vec<State>, VerificationResult> {
        let mut state = state;
        state
            .trace
            .push(format!("bb{}:term", state.ctrl.basic_block.index()));
        if let Some(assertion) = self
            .assertion_contracts
            .assertion_at(state.ctrl.basic_block, state.ctrl.statement_index)
        {
            let formula =
                self.spec_expr_to_bool(&state, &assertion.assertion, term.source_info.span)?;
            self.ensure_formula(
                &state,
                formula,
                assertion.assertion_span,
                "assertion failed".to_owned(),
            )?;
        }
        match &term.kind {
            TerminatorKind::Goto { target } => {
                self.advance_or_close_loop(state, *target, term.source_info.span)
            }
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
                    cond.as_bool()?
                } else {
                    cond.as_bool()?.not()
                };
                self.ensure_formula(
                    &state,
                    formula,
                    term.source_info.span,
                    format!("assertion failed: {msg:?}"),
                )?;
                self.advance_or_close_loop(state, *target, term.source_info.span)
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
        state: State,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        span: Span,
    ) -> Result<Vec<State>, VerificationResult> {
        let discr = self.scalar_from_operand(&state, discr, span)?;
        let mut explicit = Vec::new();
        let mut next_states = Vec::new();
        for (value, target) in targets.iter() {
            let cond = match &discr {
                TypedExpr::Bool(expr) => expr.eq(Bool::from_bool(value != 0)),
                TypedExpr::Int(expr) => expr.eq(Int::from_i64(value as i64)),
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
            if self.is_loop_backedge(state.ctrl.basic_block, target) {
                self.ensure_loop_invariant_on_reentry(&state, target, span)?;
                continue;
            }
            let mut next = self.enter_block(state.clone(), target, span)?;
            next.pc.push(cond);
            if self.path_is_feasible(&next, span)? {
                next_states.push(next);
            }
        }
        let otherwise_target = targets.otherwise();
        if self.is_loop_backedge(state.ctrl.basic_block, otherwise_target) {
            self.ensure_loop_invariant_on_reentry(&state, otherwise_target, span)?;
            return Ok(next_states);
        }
        let mut otherwise = self.enter_block(state, otherwise_target, span)?;
        let negated: Vec<_> = explicit.iter().map(|cond| cond.not()).collect();
        otherwise.pc.push(if negated.is_empty() {
            Bool::from_bool(true)
        } else {
            Bool::and(&negated.iter().collect::<Vec<_>>())
        });
        if self.path_is_feasible(&otherwise, span)? {
            next_states.push(otherwise);
        }
        Ok(next_states)
    }

    fn step_call(
        &self,
        mut state: State,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
        span: Span,
    ) -> Result<Vec<State>, VerificationResult> {
        if self.is_marker(func, "__tsuno_verify") {
            let target = target.expect("verify marker should return");
            return Ok(vec![self.enter_block(state, target, span)?]);
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
        self.advance_or_close_loop(state, target, span)
    }

    fn assign(
        &self,
        state: &mut State,
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
        state: &State,
        op: BinOp,
        lhs_operand: &Operand<'tcx>,
        rhs_operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        let lhs_ty = self.operand_ty(lhs_operand, span, state)?;
        let lhs = self.scalar_from_operand(state, lhs_operand, span)?;
        let rhs = self.scalar_from_operand(state, rhs_operand, span)?;
        let value = match op {
            BinOp::Add => SymVal::Scalar(TypedExpr::Int(lhs.as_int()? + rhs.as_int()?)),
            BinOp::Sub => SymVal::Scalar(TypedExpr::Int(lhs.as_int()? - rhs.as_int()?)),
            BinOp::Mul => SymVal::Scalar(TypedExpr::Int(lhs.as_int()? * rhs.as_int()?)),
            BinOp::Eq => SymVal::Scalar(TypedExpr::Bool(lhs.eq(&rhs)?)),
            BinOp::Ne => SymVal::Scalar(TypedExpr::Bool(lhs.eq(&rhs)?.not())),
            BinOp::Gt => SymVal::Scalar(TypedExpr::Bool(lhs.as_int()?.gt(&rhs.as_int()?))),
            BinOp::Ge => SymVal::Scalar(TypedExpr::Bool(lhs.as_int()?.ge(&rhs.as_int()?))),
            BinOp::Lt => SymVal::Scalar(TypedExpr::Bool(lhs.as_int()?.lt(&rhs.as_int()?))),
            BinOp::Le => SymVal::Scalar(TypedExpr::Bool(lhs.as_int()?.le(&rhs.as_int()?))),
            BinOp::AddWithOverflow => {
                let result = lhs.as_int()? + rhs.as_int()?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                SymVal::Pair(TypedExpr::Int(result), TypedExpr::Bool(overflow))
            }
            BinOp::SubWithOverflow => {
                let result = lhs.as_int()? - rhs.as_int()?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                SymVal::Pair(TypedExpr::Int(result), TypedExpr::Bool(overflow))
            }
            BinOp::MulWithOverflow => {
                let result = lhs.as_int()? * rhs.as_int()?;
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
        state: &State,
        op: UnOp,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
        let value = self.scalar_from_operand(state, operand, span)?;
        match op {
            UnOp::Not => Ok(TypedExpr::Bool(value.as_bool()?.not())),
            UnOp::Neg => Ok(TypedExpr::Int(-value.as_int()?)),
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
        state: &State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.read_place(state, *place, span),
            Operand::Constant(constant) => self.constant_to_symval(constant, span),
        }
    }

    fn scalar_from_operand(
        &self,
        state: &State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
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
        state: &State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
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
        state: &State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
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
        state: &mut State,
        place: Place<'tcx>,
        value: SymVal,
        span: Span,
    ) -> Result<(), VerificationResult> {
        if let Some(local) = place.as_local() {
            let loc = if let Some(loc) = state.env.get(&local).copied() {
                loc
            } else {
                let loc = self.alloc(state, SymVal::Scalar(TypedExpr::Unit));
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
        state: &State,
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

    fn mut_ref_targets(&self, state: &State, place: Place<'tcx>) -> Option<(Loc, Loc)> {
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
    ) -> Result<SymVal, VerificationResult> {
        let ty = constant.const_.ty();
        match ty.kind() {
            TyKind::Bool => {
                let value = constant.const_.try_to_bool().ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        None,
                        None,
                        "failed to evaluate boolean constant".to_owned(),
                        Vec::new(),
                    )
                })?;
                Ok(SymVal::Scalar(TypedExpr::Bool(Bool::from_bool(value))))
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
                    Int::from_i64(scalar.to_int(scalar.size()) as i64)
                } else {
                    Int::from_u64(scalar.to_uint(scalar.size()) as u64)
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
        state: &mut State,
        ty: rustc_middle::ty::Ty<'tcx>,
        prefix: &str,
    ) -> Result<SymVal, VerificationResult> {
        match ty.kind() {
            TyKind::Bool => Ok(SymVal::Scalar(TypedExpr::Bool(self.fresh_bool(prefix)))),
            TyKind::Int(_) | TyKind::Uint(_) => {
                let expr = self.fresh_int(prefix);
                if let Some(bounds) = int_range_constraint(&expr, self.tcx, ty) {
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
                    TypedExpr::Bool(self.fresh_bool(prefix)),
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
                let target = self.alloc(state, SymVal::Scalar(target_scalar.clone()));
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
        state: &mut State,
        ty: rustc_middle::ty::Ty<'tcx>,
        prefix: &str,
    ) -> Result<TypedExpr, VerificationResult> {
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

    fn fresh_bool(&self, prefix: &str) -> Bool {
        let name = format!("{prefix}_{}", self.next_sym.get());
        self.next_sym.set(self.next_sym.get() + 1);
        Bool::new_const(name)
    }

    fn fresh_int(&self, prefix: &str) -> Int {
        let name = format!("{prefix}_{}", self.next_sym.get());
        self.next_sym.set(self.next_sym.get() + 1);
        Int::new_const(name)
    }

    fn path_is_feasible(&self, state: &State, span: Span) -> Result<bool, VerificationResult> {
        let solver = self.timeout_solver();
        for cond in &state.pc {
            solver.assert(cond);
        }
        match solver.check() {
            SatResult::Sat => Ok(true),
            SatResult::Unsat => Ok(false),
            SatResult::Unknown => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                None,
                "path feasibility check returned unknown".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn is_loop_backedge(&self, source: BasicBlock, target: BasicBlock) -> bool {
        self.loop_contracts
            .contract_by_header(target)
            .is_some_and(|loop_contract| loop_contract.body_blocks.contains(&source))
    }

    fn advance_or_close_loop(
        &self,
        state: State,
        target: BasicBlock,
        span: Span,
    ) -> Result<Vec<State>, VerificationResult> {
        if self.is_loop_backedge(state.ctrl.basic_block, target) {
            self.ensure_loop_invariant_on_reentry(&state, target, span)?;
            return Ok(vec![state.goto(target)]);
        }
        Ok(vec![self.enter_block(state, target, span)?])
    }

    fn ensure_loop_invariant_on_reentry(
        &self,
        state: &State,
        header: BasicBlock,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let Some(loop_contract) = self.loop_contracts.contract_by_header(header) else {
            return Err(self.unsupported_result(
                span,
                Some(header.index()),
                None,
                "loop backedge without loop metadata".to_owned(),
                state.trace.clone(),
            ));
        };
        self.ensure_loop_invariant(state, loop_contract, span)
    }

    fn ensure_loop_invariant(
        &self,
        state: &State,
        loop_contract: &LoopContract,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let invariant = self.loop_invariant(state, loop_contract, span)?;
        self.ensure_formula(
            state,
            invariant,
            span,
            format!(
                "loop invariant does not hold for bb{} at {}",
                loop_contract.header.index(),
                self.tcx
                    .sess
                    .source_map()
                    .span_to_diagnostic_string(loop_contract.invariant_span)
            ),
        )
    }

    fn assume_loop_invariant(
        &self,
        state: &mut State,
        loop_contract: &LoopContract,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let invariant = self.loop_invariant(state, loop_contract, span)?;
        state.pc.push(invariant);
        Ok(())
    }

    fn loop_invariant(
        &self,
        state: &State,
        loop_contract: &LoopContract,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        self.spec_expr_to_bool(state, &loop_contract.invariant, span)
    }

    fn spec_expr_to_bool(
        &self,
        state: &State,
        expr: &MirSpecExpr,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match self.spec_expr_to_typed(state, expr, span)? {
            TypedExpr::Bool(expr) => Ok(expr),
            TypedExpr::Unit => Ok(Bool::from_bool(true)),
            TypedExpr::Int(_) => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "expected boolean expression".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn spec_expr_to_typed(
        &self,
        state: &State,
        expr: &MirSpecExpr,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
        match expr {
            MirSpecExpr::Bool(value) => Ok(TypedExpr::Bool(Bool::from_bool(*value))),
            MirSpecExpr::Int(value) => Ok(TypedExpr::Int(Int::from_i64(*value))),
            MirSpecExpr::Var(local) => {
                let loc = state.env.get(local).copied().ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("missing env for local {}", local.as_usize()),
                        state.trace.clone(),
                    )
                })?;
                match state.store.get(&loc).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("missing store for local {}", local.as_usize()),
                        state.trace.clone(),
                    )
                })? {
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
            MirSpecExpr::Unary { op, arg } => {
                let arg = self.spec_expr_to_typed(state, arg, span)?;
                match op {
                    crate::contracts::SpecUnaryOp::Not => Ok(TypedExpr::Bool(arg.as_bool()?.not())),
                    crate::contracts::SpecUnaryOp::Neg => Ok(TypedExpr::Int(-arg.as_int()?)),
                }
            }
            MirSpecExpr::Binary { op, lhs, rhs } => {
                let lhs = self.spec_expr_to_typed(state, lhs, span)?;
                let rhs = self.spec_expr_to_typed(state, rhs, span)?;
                match op {
                    crate::contracts::SpecBinaryOp::Add => {
                        Ok(TypedExpr::Int(lhs.as_int()? + rhs.as_int()?))
                    }
                    crate::contracts::SpecBinaryOp::Sub => {
                        Ok(TypedExpr::Int(lhs.as_int()? - rhs.as_int()?))
                    }
                    crate::contracts::SpecBinaryOp::Mul => {
                        Ok(TypedExpr::Int(lhs.as_int()? * rhs.as_int()?))
                    }
                    crate::contracts::SpecBinaryOp::Eq => Ok(TypedExpr::Bool(lhs.eq(&rhs)?)),
                    crate::contracts::SpecBinaryOp::Ne => Ok(TypedExpr::Bool(lhs.eq(&rhs)?.not())),
                    crate::contracts::SpecBinaryOp::Gt => {
                        Ok(TypedExpr::Bool(lhs.as_int()?.gt(&rhs.as_int()?)))
                    }
                    crate::contracts::SpecBinaryOp::Ge => {
                        Ok(TypedExpr::Bool(lhs.as_int()?.ge(&rhs.as_int()?)))
                    }
                    crate::contracts::SpecBinaryOp::Lt => {
                        Ok(TypedExpr::Bool(lhs.as_int()?.lt(&rhs.as_int()?)))
                    }
                    crate::contracts::SpecBinaryOp::Le => {
                        Ok(TypedExpr::Bool(lhs.as_int()?.le(&rhs.as_int()?)))
                    }
                    crate::contracts::SpecBinaryOp::And => {
                        let lhs = lhs.as_bool()?;
                        let rhs = rhs.as_bool()?;
                        Ok(TypedExpr::Bool(Bool::and(&[&lhs, &rhs])))
                    }
                    crate::contracts::SpecBinaryOp::Or => {
                        let lhs = lhs.as_bool()?;
                        let rhs = rhs.as_bool()?;
                        Ok(TypedExpr::Bool(Bool::or(&[&lhs, &rhs])))
                    }
                }
            }
        }
    }

    fn enter_block(
        &self,
        mut state: State,
        target: BasicBlock,
        span: Span,
    ) -> Result<State, VerificationResult> {
        if let Some(header) = self.loop_contracts.header_for_invariant_block(target) {
            let Some(loop_contract) = self.loop_contracts.contract_by_header(header) else {
                return Err(self.unsupported_result(
                    span,
                    Some(target.index()),
                    Some(state.ctrl.statement_index),
                    "loop body is missing contract metadata".to_owned(),
                    state.trace.clone(),
                ));
            };
            self.assume_loop_invariant(&mut state, loop_contract, span)?;
        }
        Ok(state.goto(target))
    }

    fn is_marker(&self, operand: &Operand<'tcx>, suffix: &str) -> bool {
        let Some(def_id) = call_target_def_id(operand) else {
            return false;
        };
        self.tcx.def_path_str(def_id).contains(suffix)
    }

    fn ensure_formula(
        &self,
        state: &State,
        formula: Bool,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let solver = self.timeout_solver();
        for cond in &state.pc {
            solver.assert(cond);
        }
        solver.assert(formula.not());
        match solver.check() {
            SatResult::Sat => {
                let model = solver
                    .get_model()
                    .map(|model| vec![("model".to_owned(), model.to_string())])
                    .unwrap_or_default();
                Err(VerificationResult {
                    function: self.tcx.def_path_str(self.def_id.to_def_id()),
                    status: VerificationStatus::Fail,
                    span: span_text(self.tcx, span),
                    basic_block: Some(state.ctrl.basic_block.index()),
                    statement_index: Some(state.ctrl.statement_index),
                    message,
                    trace: state.trace.clone(),
                    model,
                })
            }
            SatResult::Unsat => Ok(()),
            SatResult::Unknown => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "solver returned unknown while checking assertion".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn place_ty(&self, place: Place<'tcx>) -> rustc_middle::ty::Ty<'tcx> {
        place.ty(&self.body, self.tcx).ty
    }

    fn operand_ty(
        &self,
        operand: &Operand<'tcx>,
        span: Span,
        state: &State,
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
        result: &Int,
        ty: rustc_middle::ty::Ty<'tcx>,
        span: Span,
        state: &State,
    ) -> Result<Bool, VerificationResult> {
        match int_bounds(self.tcx, ty) {
            Some(IntBounds::Signed { min, max }) => {
                let low = result.lt(Int::from_i64(min));
                let high = result.gt(Int::from_i64(max));
                Ok(Bool::or(&[&low, &high]))
            }
            Some(IntBounds::Unsigned { max }) => {
                let low = result.lt(Int::from_i64(0));
                let high = result.gt(Int::from_u64(max));
                Ok(Bool::or(&[&low, &high]))
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

    fn initial_state(&self) -> State {
        let mut state = State::empty();
        for local in self.body.local_decls.indices() {
            let ty = self.body.local_decls[local].ty;
            let value = self
                .fresh_symval_for_ty(&mut state, ty, &format!("arg_{}", local.as_usize()))
                .unwrap_or(SymVal::Scalar(TypedExpr::Unit));
            let loc = self.alloc(&mut state, value);
            state.env.insert(local, loc);
        }
        state
    }

    fn alloc(&self, state: &mut State, value: SymVal) -> Loc {
        let loc = Loc(self.next_loc.get());
        self.next_loc.set(self.next_loc.get() + 1);
        state.store.insert(loc, value);
        loc
    }

    fn enqueue_state(
        &self,
        pending: &mut BTreeMap<ControlPoint, Vec<State>>,
        worklist: &mut VecDeque<ControlPoint>,
        state: State,
    ) {
        let ctrl = state.ctrl;
        let bucket = pending.entry(ctrl).or_default();
        if bucket.is_empty() {
            bucket.push(state);
            worklist.push_back(ctrl);
            return;
        }
        bucket.push(state);
    }

    fn timeout_solver(&self) -> Solver {
        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);
        solver
    }

    fn merge_symval(&self, guard: &Bool, existing: &SymVal, incoming: &SymVal) -> Option<SymVal> {
        match (existing, incoming) {
            (SymVal::Scalar(existing), SymVal::Scalar(incoming)) => Some(SymVal::Scalar(
                self.merge_typed_expr(guard, existing, incoming)?,
            )),
            (SymVal::Pair(existing_a, existing_b), SymVal::Pair(incoming_a, incoming_b)) => {
                Some(SymVal::Pair(
                    self.merge_typed_expr(guard, existing_a, incoming_a)?,
                    self.merge_typed_expr(guard, existing_b, incoming_b)?,
                ))
            }
            (
                SymVal::MutRef {
                    target: existing_target,
                    cur: existing_cur,
                    fin: existing_fin,
                },
                SymVal::MutRef {
                    target: incoming_target,
                    cur: incoming_cur,
                    fin: incoming_fin,
                },
            ) if existing_target == incoming_target => Some(SymVal::MutRef {
                target: *existing_target,
                cur: self.merge_typed_expr(guard, existing_cur, incoming_cur)?,
                fin: self.merge_typed_expr(guard, existing_fin, incoming_fin)?,
            }),
            _ => None,
        }
    }

    fn merge_typed_expr(
        &self,
        guard: &Bool,
        existing: &TypedExpr,
        incoming: &TypedExpr,
    ) -> Option<TypedExpr> {
        if same_typed_expr(existing, incoming) {
            return Some(existing.clone());
        }
        match (existing, incoming) {
            (TypedExpr::Bool(existing), TypedExpr::Bool(incoming)) => {
                Some(TypedExpr::Bool(guard.ite(incoming, existing)))
            }
            (TypedExpr::Int(existing), TypedExpr::Int(incoming)) => {
                Some(TypedExpr::Int(guard.ite(incoming, existing)))
            }
            (TypedExpr::Unit, TypedExpr::Unit) => Some(TypedExpr::Unit),
            _ => None,
        }
    }

    fn close_live_mut_refs(&self, state: &mut State, span: Span) -> Result<(), VerificationResult> {
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
        state: &mut State,
        local: Local,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let Some(loc) = state.env.get(&local).copied() else {
            return Ok(());
        };
        let Some(value) = state.store.get(&loc).cloned() else {
            return Ok(());
        };
        let SymVal::MutRef { target, cur, fin } = value else {
            return Ok(());
        };
        self.ensure_formula(
            state,
            cur.eq(&fin)?,
            span,
            "mutable reference close failed".to_owned(),
        )?;
        state.store.insert(target, SymVal::Scalar(cur));
        state.store.insert(loc, SymVal::Scalar(TypedExpr::Unit));
        Ok(())
    }
}

impl State {
    fn empty() -> Self {
        Self {
            env: BTreeMap::new(),
            store: BTreeMap::new(),
            pc: Vec::new(),
            ctrl: ControlPoint {
                basic_block: BasicBlock::from_usize(0),
                statement_index: 0,
            },
            trace: Vec::new(),
        }
    }

    fn goto(mut self, target: BasicBlock) -> Self {
        self.ctrl = ControlPoint {
            basic_block: target,
            statement_index: 0,
        };
        self
    }
}

impl TypedExpr {
    fn as_bool(&self) -> Result<Bool, VerificationResult> {
        match self {
            TypedExpr::Bool(expr) => Ok(expr.clone()),
            TypedExpr::Unit => Ok(Bool::from_bool(true)),
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

    fn as_int(&self) -> Result<Int, VerificationResult> {
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

    fn eq(&self, rhs: &Self) -> Result<Bool, VerificationResult> {
        match (self, rhs) {
            (TypedExpr::Bool(lhs), TypedExpr::Bool(rhs)) => Ok(lhs.eq(rhs)),
            (TypedExpr::Int(lhs), TypedExpr::Int(rhs)) => Ok(lhs.eq(rhs)),
            (TypedExpr::Unit, TypedExpr::Unit) => Ok(Bool::from_bool(true)),
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

pub fn default_z3() {
    set_global_param("model", "true");
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

fn int_range_constraint(expr: &Int, tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> Option<Bool> {
    match int_bounds(tcx, ty)? {
        IntBounds::Signed { min, max } => {
            let low = expr.ge(Int::from_i64(min));
            let high = expr.le(Int::from_i64(max));
            Some(Bool::and(&[&low, &high]))
        }
        IntBounds::Unsigned { max } => {
            let low = expr.ge(Int::from_i64(0));
            let high = expr.le(Int::from_u64(max));
            Some(Bool::and(&[&low, &high]))
        }
    }
}

fn common_prefix(left: &[String], right: &[String]) -> Vec<String> {
    left.iter()
        .zip(right.iter())
        .take_while(|(l, r)| l == r)
        .map(|(item, _)| item.clone())
        .collect()
}

fn same_typed_expr(left: &TypedExpr, right: &TypedExpr) -> bool {
    match (left, right) {
        (TypedExpr::Bool(left), TypedExpr::Bool(right)) => left.to_string() == right.to_string(),
        (TypedExpr::Int(left), TypedExpr::Int(right)) => left.to_string() == right.to_string(),
        (TypedExpr::Unit, TypedExpr::Unit) => true,
        _ => false,
    }
}
