#![allow(clippy::result_large_err)]

use std::cell::Cell;
use std::collections::{BTreeMap, HashMap, VecDeque};

use rustc_hir::def_id::LocalDefId;
use rustc_hir::{ItemKind, PatKind};
use rustc_middle::mir::{
    AggregateKind, BasicBlock, BinOp, Body, BorrowKind, ConstOperand, Local, Operand, Place,
    PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::ty::{IntTy, TyCtxt, TyKind, UintTy};
use rustc_span::Span;
use rustc_span::source_map::Spanned;
use syn::{Expr as SynExpr, Lit, LitStr};
use z3::ast::{Bool, Int};
use z3::{SatResult, Solver, set_global_param};

use crate::directive::{SpecBinaryOp, SpecUnaryOp, parse_spec_template};
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
    store: BTreeMap<Loc, Slot>,
    pc: Vec<Bool>,
    assertion: Vec<Bool>,
    live: BTreeMap<Local, bool>,
    ctrl: ControlPoint,
    trace: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ControlPoint {
    basic_block: BasicBlock,
    statement_index: usize,
}

#[derive(Debug, Clone)]
pub enum Slot {
    Live(SymVal),
    Moved,
}

#[derive(Debug, Clone)]
pub enum SymVal {
    Scalar(TypedExpr),
    Tuple(Box<[Loc]>),
    MutRef {
        target: Loc,
        cur: Box<SymVal>,
        fin: Box<SymVal>,
    },
}

#[derive(Debug, Clone)]
pub enum TypedExpr {
    Bool(Bool),
    Int(Int),
    Tuple(Box<[TypedExpr]>),
}

#[derive(Debug, Clone)]
struct FunctionContract {
    params: Vec<String>,
    req: ContractExpr,
    ens: ContractExpr,
}

#[derive(Debug, Clone)]
enum ContractExpr {
    Bool(bool),
    Int(i64),
    Var(String),
    Prophecy(String),
    Unary {
        op: SpecUnaryOp,
        arg: Box<ContractExpr>,
    },
    Binary {
        op: SpecBinaryOp,
        lhs: Box<ContractExpr>,
        rhs: Box<ContractExpr>,
    },
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: Body<'tcx>,
    solver: Solver,
    contracts: HashMap<LocalDefId, FunctionContract>,
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
        let contracts = match collect_function_contracts(tcx) {
            Ok(contracts) => contracts,
            Err(error) => {
                prepass_error.get_or_insert(error);
                HashMap::new()
            }
        };
        Self {
            tcx,
            def_id,
            body,
            solver: {
                let solver = Solver::new();
                let mut params = z3::Params::new();
                params.set_u32("timeout", 1_000);
                solver.set_params(&params);
                solver
            },
            contracts,
            loop_contracts,
            assertion_contracts,
            prepass_error,
            switch_joins,
            next_loc: Cell::new(0),
            next_sym: Cell::new(0),
        }
    }

    pub fn verify(&self) -> VerificationResult {
        if let Some(result) = self.prepass_error.clone() {
            return result;
        }
        let mut pending: BTreeMap<ControlPoint, Vec<State>> = BTreeMap::new();
        let mut worklist = VecDeque::new();
        let initial_state = match self.initial_state() {
            Ok(initial_state) => initial_state,
            Err(result) => return result,
        };
        self.enqueue_state(&mut pending, &mut worklist, initial_state);
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
                merged.assertion.clear();
                merged.live = first.live.clone();
                for state in &bucket {
                    let guard = state.pc.get(common_len).cloned().expect(
                        "join bucket must have a branch guard at the first divergent pc element",
                    );
                    for cond in &state.pc[common_len + 1..] {
                        merged.pc.push(guard.implies(cond));
                    }
                    let state_assertion = if state.assertion.is_empty() {
                        Bool::from_bool(true)
                    } else {
                        let refs: Vec<_> = state.assertion.iter().collect();
                        Bool::and(&refs)
                    };
                    let state_pc = if state.pc.is_empty() {
                        Bool::from_bool(true)
                    } else {
                        let refs: Vec<_> = state.pc.iter().collect();
                        Bool::and(&refs)
                    };
                    merged.assertion.push(state_pc.implies(&state_assertion));
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
                    let first_slot = first
                        .store
                        .get(&first_loc)
                        .cloned()
                        .expect("shared local missing from first branch store");
                    let mut merged_value = self
                        .clone_slot_into_state(&mut merged, &first, &first_slot)
                        .expect("join bucket value shape mismatch");
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
                        let existing_state = merged.clone();
                        merged_value = self
                            .merge_slot(
                                &mut merged,
                                &guard,
                                &existing_state,
                                &merged_value,
                                state,
                                &incoming_value,
                            )
                            .expect("join bucket value shape mismatch");
                    }
                    let loc = self.alloc_slot(&mut merged, merged_value);
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
                formula.clone(),
                assertion.assertion_span,
                "assertion failed".to_owned(),
            )?;
            state.assertion.push(formula);
        }
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                if state.live.get(local).copied().unwrap_or(false) {
                    self.close_local(&mut state, *local, stmt.source_info.span)?;
                    state.env.remove(local);
                }
                let value = self.fresh_symval_for_ty(
                    &mut state,
                    self.body.local_decls[*local].ty,
                    &format!("live_{}", local.as_usize()),
                )?;
                let loc = self.alloc(&mut state, value);
                state.env.insert(*local, loc);
                state.live.insert(*local, true);
            }
            StatementKind::StorageDead(local) => {
                if !state.live.get(local).copied().unwrap_or(false) {
                    // already unallocated
                } else {
                    self.close_local(&mut state, *local, stmt.source_info.span)?;
                    state.live.insert(*local, false);
                }
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
                formula.clone(),
                assertion.assertion_span,
                "assertion failed".to_owned(),
            )?;
            state.assertion.push(formula);
        }
        match &term.kind {
            TerminatorKind::Goto { target } => {
                self.advance_or_close_loop(state, *target, term.source_info.span)
            }
            TerminatorKind::Return => {
                if let Some(contract) = self.contracts.get(&self.def_id) {
                    let mut env = HashMap::new();
                    for (name, local) in contract
                        .params
                        .iter()
                        .cloned()
                        .zip(self.body.local_decls.indices().skip(1))
                    {
                        let Some(loc) = state.env.get(&local).copied() else {
                            return Err(self.unsupported_result(
                                term.source_info.span,
                                Some(state.ctrl.basic_block.index()),
                                Some(state.ctrl.statement_index),
                                format!("missing env for local {}", local.as_usize()),
                                state.trace.clone(),
                            ));
                        };
                        let Some(Slot::Live(value)) = state.store.get(&loc).cloned() else {
                            return Err(self.unsupported_result(
                                term.source_info.span,
                                Some(state.ctrl.basic_block.index()),
                                Some(state.ctrl.statement_index),
                                format!("missing store for local {}", local.as_usize()),
                                state.trace.clone(),
                            ));
                        };
                        env.insert(name, value);
                    }
                    let result_local = Local::from_usize(0);
                    let Some(result_loc) = state.env.get(&result_local).copied() else {
                        return Err(self.unsupported_result(
                            term.source_info.span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "missing return local".to_owned(),
                            state.trace.clone(),
                        ));
                    };
                    let Some(Slot::Live(result_value)) = state.store.get(&result_loc).cloned()
                    else {
                        return Err(self.unsupported_result(
                            term.source_info.span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "missing return value".to_owned(),
                            state.trace.clone(),
                        ));
                    };
                    env.insert("result".to_owned(), result_value);
                    let ens = self.contract_expr_to_bool(
                        &state,
                        &contract.ens,
                        &env,
                        term.source_info.span,
                    )?;
                    self.ensure_formula(
                        &state,
                        ens,
                        term.source_info.span,
                        "postcondition failed".to_owned(),
                    )?;
                }
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
                let cond = self.scalar_from_operand(&mut state, cond, term.source_info.span)?;
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
        mut state: State,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        span: Span,
    ) -> Result<Vec<State>, VerificationResult> {
        let discr = self.scalar_from_operand(&mut state, discr, span)?;
        let mut explicit = Vec::new();
        let mut next_states = Vec::new();
        for (value, target) in targets.iter() {
            let cond = match &discr {
                TypedExpr::Bool(expr) => expr.eq(Bool::from_bool(value != 0)),
                TypedExpr::Int(expr) => expr.eq(Int::from_i64(value as i64)),
                TypedExpr::Tuple(_) => {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        None,
                        "switch on tuple is unsupported".to_owned(),
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
        let callee_def_id = self.called_def_id(func);
        let contract = callee_def_id.and_then(|def_id| self.contracts.get(&def_id));
        let pre_call_args = if let Some(contract) = contract {
            let mut env = HashMap::new();
            if contract.params.len() != args.len() {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    None,
                    format!(
                        "call contract parameter count mismatch: expected {}, found {}",
                        contract.params.len(),
                        args.len()
                    ),
                    state.trace.clone(),
                ));
            }
            for (name, arg) in contract.params.iter().cloned().zip(args.iter()) {
                let value = self.operand_to_contract_symval(&state, &arg.node, span)?;
                env.insert(name, value);
            }
            Some(env)
        } else {
            None
        };
        if let (Some(contract), Some(env)) = (contract, pre_call_args.as_ref()) {
            let req = self.contract_expr_to_bool(&state, &contract.req, env, span)?;
            state.pc.push(req);
            if !self.path_is_feasible(&state, span)? {
                return Ok(Vec::new());
            }
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
                let fresh = self.fresh_symval_for_ty(&mut state, target_ty, "call_mut")?;
                let Some(Slot::Live(SymVal::MutRef { target, cur, .. })) =
                    state.store.get(&base_loc).cloned()
                else {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        None,
                        "missing mutable reference argument".to_owned(),
                        state.trace.clone(),
                    ));
                };
                state.store.insert(
                    base_loc,
                    Slot::Live(SymVal::MutRef {
                        target: target_loc,
                        cur,
                        fin: Box::new(fresh.clone()),
                    }),
                );
                state.store.insert(target_loc, Slot::Live(fresh.clone()));
                self.update_mutref_aliases(&mut state, target, None, Some(&fresh));
                state.store.insert(base_loc, Slot::Moved);
            }
        }
        let value = self.fresh_symval_for_ty(&mut state, self.place_ty(destination), "call_ret")?;
        self.write_place(&mut state, destination, value, span)?;
        if let Some(contract) = contract {
            let mut env = HashMap::new();
            for (name, arg) in contract.params.iter().cloned().zip(args.iter()) {
                let value = self.operand_to_contract_symval(&state, &arg.node, span)?;
                env.insert(name, value);
            }
            let result_value = self.read_place(&state, destination, span)?;
            env.insert("result".to_owned(), result_value);
            let ens = self.contract_expr_to_bool(&state, &contract.ens, &env, span)?;
            state.assertion.push(ens);
        }
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

    fn called_def_id(&self, func: &Operand<'tcx>) -> Option<LocalDefId> {
        let Operand::Constant(constant) = func else {
            return None;
        };
        let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
            return None;
        };
        def_id.as_local()
    }

    fn operand_to_contract_symval(
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
            Rvalue::Aggregate(kind, operands) => match kind.as_ref() {
                AggregateKind::Tuple => {
                    let mut locs = Vec::with_capacity(operands.len());
                    for operand in operands.iter() {
                        let value = self.operand_to_symval(state, operand, span)?;
                        let loc = self.alloc(state, value);
                        locs.push(loc);
                    }
                    if locs.is_empty() {
                        SymVal::Scalar(TypedExpr::Tuple(Vec::new().into_boxed_slice()))
                    } else {
                        SymVal::Tuple(locs.into_boxed_slice())
                    }
                }
                other => {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("unsupported aggregate kind {other:?}"),
                        state.trace.clone(),
                    ));
                }
            },
            Rvalue::Ref(_, borrow_kind, borrowed_place) => match borrow_kind {
                BorrowKind::Mut { .. } => {
                    let target = self.place_loc(state, *borrowed_place, span)?;
                    let current = self.read_place(state, *borrowed_place, span)?;
                    SymVal::MutRef {
                        target,
                        cur: Box::new(current.clone()),
                        fin: Box::new(current),
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
        state: &mut State,
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
                let first = self.alloc(state, SymVal::Scalar(TypedExpr::Int(result)));
                let second = self.alloc(state, SymVal::Scalar(TypedExpr::Bool(overflow)));
                SymVal::Tuple(vec![first, second].into_boxed_slice())
            }
            BinOp::SubWithOverflow => {
                let result = lhs.as_int()? - rhs.as_int()?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                let first = self.alloc(state, SymVal::Scalar(TypedExpr::Int(result)));
                let second = self.alloc(state, SymVal::Scalar(TypedExpr::Bool(overflow)));
                SymVal::Tuple(vec![first, second].into_boxed_slice())
            }
            BinOp::MulWithOverflow => {
                let result = lhs.as_int()? * rhs.as_int()?;
                let overflow = self.overflow_formula(&result, lhs_ty, span, state)?;
                let first = self.alloc(state, SymVal::Scalar(TypedExpr::Int(result)));
                let second = self.alloc(state, SymVal::Scalar(TypedExpr::Bool(overflow)));
                SymVal::Tuple(vec![first, second].into_boxed_slice())
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
        state: &mut State,
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
        state: &mut State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        match operand {
            Operand::Copy(place) => self.read_place(state, *place, span),
            Operand::Move(place) if self.place_is_copy(*place) => {
                self.read_place(state, *place, span)
            }
            Operand::Move(place) => self.take_place(state, *place, span),
            Operand::Constant(constant) => self.constant_to_symval(constant, span),
        }
    }

    fn scalar_from_operand(
        &self,
        state: &mut State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
        match self.operand_to_symval(state, operand, span)? {
            SymVal::Scalar(expr) => Ok(expr),
            SymVal::MutRef { cur, .. } => match cur.as_ref() {
                SymVal::Scalar(expr) => Ok(expr.clone()),
                _ => Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    "tuple value used where scalar was expected".to_owned(),
                    state.trace.clone(),
                )),
            },
            SymVal::Tuple(..) => Err(self.unsupported_result(
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
            SymVal::MutRef { cur, .. } => match cur.as_ref() {
                SymVal::Scalar(expr) => Ok(expr.clone()),
                _ => Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    "tuple value used where scalar was expected".to_owned(),
                    state.trace.clone(),
                )),
            },
            SymVal::Tuple(..) => Err(self.unsupported_result(
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
            if !state.live.get(&local).copied().unwrap_or(false) {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("use of dead value {}", local.as_usize()),
                    state.trace.clone(),
                ));
            }
            return match state.store.get(&loc).cloned() {
                Some(Slot::Moved) => Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("use of moved value {}", local.as_usize()),
                    state.trace.clone(),
                )),
                Some(Slot::Live(value)) => Ok(value),
                None => Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("missing store for local {}", local.as_usize()),
                    state.trace.clone(),
                )),
            };
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
                let target = match state.store.get(&loc).cloned() {
                    Some(Slot::Live(SymVal::MutRef { target, .. })) => target,
                    Some(Slot::Moved) => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "use of moved value".to_owned(),
                            state.trace.clone(),
                        ));
                    }
                    Some(Slot::Live(_)) => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "deref of non-mutable reference".to_owned(),
                            state.trace.clone(),
                        ));
                    }
                    None => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "missing mutable reference".to_owned(),
                            state.trace.clone(),
                        ));
                    }
                };
                match state.store.get(&target).cloned() {
                    Some(Slot::Moved) => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "use of moved value".to_owned(),
                        state.trace.clone(),
                    )),
                    Some(Slot::Live(value)) => Ok(value),
                    None => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "missing deref target".to_owned(),
                        state.trace.clone(),
                    )),
                }
            }
            PlaceElem::Field(field, _) => {
                let base_place = base.to_place(self.tcx);
                let base_value = self.read_place(state, base_place, span)?;
                let field_loc = match base_value {
                    SymVal::Tuple(fields) => match fields.get(field.index()) {
                        Some(loc) => *loc,
                        None => {
                            return Err(self.unsupported_result(
                                span,
                                Some(state.ctrl.basic_block.index()),
                                Some(state.ctrl.statement_index),
                                format!("unsupported tuple field {}", field.index()),
                                state.trace.clone(),
                            ));
                        }
                    },
                    other => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            format!("field projection on unsupported value {other:?}"),
                            state.trace.clone(),
                        ));
                    }
                };
                match state.store.get(&field_loc).cloned() {
                    Some(Slot::Moved) => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "use of moved value".to_owned(),
                        state.trace.clone(),
                    )),
                    Some(Slot::Live(value)) => Ok(value),
                    None => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "missing tuple field".to_owned(),
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

    fn take_place(
        &self,
        state: &mut State,
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
            if !state.live.get(&local).copied().unwrap_or(false) {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("use of dead value {}", local.as_usize()),
                    state.trace.clone(),
                ));
            }
            let Some(slot) = state.store.get_mut(&loc) else {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("missing store for local {}", local.as_usize()),
                    state.trace.clone(),
                ));
            };
            return slot.take().ok_or_else(|| {
                self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("use of moved value {}", local.as_usize()),
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
            PlaceElem::Field(field, _) => {
                let base_place = base.to_place(self.tcx);
                let base_value = self.read_place(state, base_place, span)?;
                let field_loc = match base_value {
                    SymVal::Tuple(fields) => match fields.get(field.index()) {
                        Some(loc) => *loc,
                        None => {
                            return Err(self.unsupported_result(
                                span,
                                Some(state.ctrl.basic_block.index()),
                                Some(state.ctrl.statement_index),
                                format!("unsupported tuple field {}", field.index()),
                                state.trace.clone(),
                            ));
                        }
                    },
                    other => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            format!("field projection on unsupported value {other:?}"),
                            state.trace.clone(),
                        ));
                    }
                };
                let Some(slot) = state.store.get_mut(&field_loc) else {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "missing tuple field".to_owned(),
                        state.trace.clone(),
                    ));
                };
                slot.take().ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "use of moved value".to_owned(),
                        state.trace.clone(),
                    )
                })
            }
            PlaceElem::Deref => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "move through deref is unsupported".to_owned(),
                state.trace.clone(),
            )),
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
                if !state.live.get(&local).copied().unwrap_or(false) {
                    return Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("write to dead value {}", local.as_usize()),
                        state.trace.clone(),
                    ));
                }
                loc
            } else {
                let loc = self.alloc(
                    state,
                    SymVal::Scalar(TypedExpr::Tuple(Vec::new().into_boxed_slice())),
                );
                state.env.insert(local, loc);
                state.live.insert(local, true);
                loc
            };
            state.store.insert(loc, Slot::Live(value));
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
                    Some(Slot::Live(SymVal::MutRef { target, .. })) => *target,
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
                state.store.insert(
                    base_loc,
                    Slot::Live(SymVal::MutRef {
                        target,
                        cur: Box::new(value.clone()),
                        fin: Box::new(value.clone()),
                    }),
                );
                state.store.insert(target, Slot::Live(value.clone()));
                self.update_mutref_aliases(state, target, Some(&value), Some(&value));
                Ok(())
            }
            PlaceElem::Field(field, _) => {
                let base_place = base.to_place(self.tcx);
                let base_value = self.read_place(state, base_place, span)?;
                let field_loc = match base_value {
                    SymVal::Tuple(fields) => match fields.get(field.index()) {
                        Some(loc) => *loc,
                        None => {
                            return Err(self.unsupported_result(
                                span,
                                Some(state.ctrl.basic_block.index()),
                                Some(state.ctrl.statement_index),
                                format!("unsupported tuple field {}", field.index()),
                                state.trace.clone(),
                            ));
                        }
                    },
                    other => {
                        return Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            format!("field write on unsupported value {other:?}"),
                            state.trace.clone(),
                        ));
                    }
                };
                state.store.insert(field_loc, Slot::Live(value));
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
            if !state.live.get(&local).copied().unwrap_or(false) {
                return Err(self.unsupported_result(
                    span,
                    Some(state.ctrl.basic_block.index()),
                    Some(state.ctrl.statement_index),
                    format!("use of dead value {}", local.as_usize()),
                    state.trace.clone(),
                ));
            }
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
        let Some((base, elem)) = place.as_ref().last_projection() else {
            return Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "unsupported place loc".to_owned(),
                state.trace.clone(),
            ));
        };
        match elem {
            PlaceElem::Deref => {
                let base_place = base.to_place(self.tcx);
                let base_loc = self.place_loc(state, base_place, span)?;
                match state.store.get(&base_loc) {
                    Some(Slot::Live(SymVal::MutRef { target, .. })) => Ok(*target),
                    Some(Slot::Moved) => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "use of moved value".to_owned(),
                        state.trace.clone(),
                    )),
                    _ => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "deref loc through non-mutable reference".to_owned(),
                        state.trace.clone(),
                    )),
                }
            }
            PlaceElem::Field(field, _) => {
                let base_place = base.to_place(self.tcx);
                let base_value = self.read_place(state, base_place, span)?;
                match base_value {
                    SymVal::Tuple(fields) => match fields.get(field.index()) {
                        Some(loc) => Ok(*loc),
                        None => Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            format!("unsupported tuple field {}", field.index()),
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

    fn mut_ref_targets(&self, state: &State, place: Place<'tcx>) -> Option<(Loc, Loc)> {
        let local = place.as_local()?;
        if !state.live.get(&local).copied().unwrap_or(false) {
            return None;
        }
        let base_loc = state.env.get(&local).copied()?;
        match state.store.get(&base_loc) {
            Some(Slot::Live(SymVal::MutRef { target, .. })) => Some((base_loc, *target)),
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
            TyKind::Tuple(fields) if fields.is_empty() => Ok(SymVal::Scalar(TypedExpr::Tuple(
                Vec::new().into_boxed_slice(),
            ))),
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
            TyKind::Tuple(fields) if fields.is_empty() => Ok(SymVal::Scalar(TypedExpr::Tuple(
                Vec::new().into_boxed_slice(),
            ))),
            TyKind::Tuple(fields) => {
                let mut locs = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    let value = self.fresh_symval_for_ty(state, field, prefix)?;
                    let loc = self.alloc(state, value);
                    locs.push(loc);
                }
                Ok(SymVal::Tuple(locs.into_boxed_slice()))
            }
            TyKind::Ref(_, inner, rustc_middle::mir::Mutability::Mut) => {
                let target_value = self.fresh_symval_for_ty(state, *inner, prefix)?;
                let target = self.alloc(state, target_value.clone());
                Ok(SymVal::MutRef {
                    target,
                    cur: Box::new(target_value.clone()),
                    fin: Box::new(target_value),
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
        self.solver.push();
        for cond in &state.pc {
            self.solver.assert(cond);
        }
        for cond in &state.assertion {
            self.solver.assert(cond);
        }
        let result = match self.solver.check() {
            SatResult::Sat => Ok(true),
            SatResult::Unsat => Ok(false),
            SatResult::Unknown => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                None,
                "path feasibility check returned unknown".to_owned(),
                state.trace.clone(),
            )),
        };
        self.solver.pop(1);
        result
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
            TypedExpr::Tuple(fields) if fields.is_empty() => Ok(Bool::from_bool(true)),
            TypedExpr::Tuple(_) => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "expected boolean expression".to_owned(),
                state.trace.clone(),
            )),
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
            MirSpecExpr::Result | MirSpecExpr::Prophecy(_) => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "contract-only expression used in MIR assertion".to_owned(),
                state.trace.clone(),
            )),
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
                    Slot::Live(SymVal::Scalar(expr)) => Ok(expr),
                    Slot::Live(SymVal::MutRef { cur, .. }) => match cur.as_ref() {
                        SymVal::Scalar(expr) => Ok(expr.clone()),
                        SymVal::MutRef { .. } | SymVal::Tuple(..) => Err(self.unsupported_result(
                            span,
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "tuple value used where scalar was expected".to_owned(),
                            state.trace.clone(),
                        )),
                    },
                    Slot::Live(SymVal::Tuple(..)) => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "tuple value used where scalar was expected".to_owned(),
                        state.trace.clone(),
                    )),
                    Slot::Moved => Err(self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        "use of moved value".to_owned(),
                        state.trace.clone(),
                    )),
                }
            }
            MirSpecExpr::Unary { op, arg } => {
                let arg = self.spec_expr_to_typed(state, arg, span)?;
                match op {
                    SpecUnaryOp::Not => Ok(TypedExpr::Bool(arg.as_bool()?.not())),
                    SpecUnaryOp::Neg => Ok(TypedExpr::Int(-arg.as_int()?)),
                }
            }
            MirSpecExpr::Binary { op, lhs, rhs } => {
                let lhs = self.spec_expr_to_typed(state, lhs, span)?;
                let rhs = self.spec_expr_to_typed(state, rhs, span)?;
                match op {
                    SpecBinaryOp::Add => Ok(TypedExpr::Int(lhs.as_int()? + rhs.as_int()?)),
                    SpecBinaryOp::Sub => Ok(TypedExpr::Int(lhs.as_int()? - rhs.as_int()?)),
                    SpecBinaryOp::Mul => Ok(TypedExpr::Int(lhs.as_int()? * rhs.as_int()?)),
                    SpecBinaryOp::Eq => Ok(TypedExpr::Bool(lhs.eq(&rhs)?)),
                    SpecBinaryOp::Ne => Ok(TypedExpr::Bool(lhs.eq(&rhs)?.not())),
                    SpecBinaryOp::Gt => Ok(TypedExpr::Bool(lhs.as_int()?.gt(&rhs.as_int()?))),
                    SpecBinaryOp::Ge => Ok(TypedExpr::Bool(lhs.as_int()?.ge(&rhs.as_int()?))),
                    SpecBinaryOp::Lt => Ok(TypedExpr::Bool(lhs.as_int()?.lt(&rhs.as_int()?))),
                    SpecBinaryOp::Le => Ok(TypedExpr::Bool(lhs.as_int()?.le(&rhs.as_int()?))),
                    SpecBinaryOp::And => {
                        let lhs = lhs.as_bool()?;
                        let rhs = rhs.as_bool()?;
                        Ok(TypedExpr::Bool(Bool::and(&[&lhs, &rhs])))
                    }
                    SpecBinaryOp::Or => {
                        let lhs = lhs.as_bool()?;
                        let rhs = rhs.as_bool()?;
                        Ok(TypedExpr::Bool(Bool::or(&[&lhs, &rhs])))
                    }
                }
            }
        }
    }

    fn contract_expr_to_bool(
        &self,
        state: &State,
        expr: &ContractExpr,
        env: &HashMap<String, SymVal>,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match self.contract_expr_to_typed(state, expr, env, span)? {
            TypedExpr::Bool(expr) => Ok(expr),
            TypedExpr::Tuple(fields) if fields.is_empty() => Ok(Bool::from_bool(true)),
            TypedExpr::Tuple(_) | TypedExpr::Int(_) => Err(self.unsupported_result(
                span,
                Some(state.ctrl.basic_block.index()),
                Some(state.ctrl.statement_index),
                "expected boolean expression".to_owned(),
                state.trace.clone(),
            )),
        }
    }

    fn contract_expr_to_typed(
        &self,
        state: &State,
        expr: &ContractExpr,
        env: &HashMap<String, SymVal>,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
        match expr {
            ContractExpr::Bool(value) => Ok(TypedExpr::Bool(Bool::from_bool(*value))),
            ContractExpr::Int(value) => Ok(TypedExpr::Int(Int::from_i64(*value))),
            ContractExpr::Var(name) => {
                let value = env.get(name).ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("missing contract binding `{name}`"),
                        state.trace.clone(),
                    )
                })?;
                value.to_typed_current(state, span)
            }
            ContractExpr::Prophecy(name) => {
                let value = env.get(name).ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        Some(state.ctrl.basic_block.index()),
                        Some(state.ctrl.statement_index),
                        format!("missing contract binding `{name}`"),
                        state.trace.clone(),
                    )
                })?;
                value.to_typed_prophecy(state, span)
            }
            ContractExpr::Unary { op, arg } => {
                let arg = self.contract_expr_to_typed(state, arg, env, span)?;
                match op {
                    SpecUnaryOp::Not => Ok(TypedExpr::Bool(arg.as_bool()?.not())),
                    SpecUnaryOp::Neg => Ok(TypedExpr::Int(-arg.as_int()?)),
                }
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let lhs = self.contract_expr_to_typed(state, lhs, env, span)?;
                let rhs = self.contract_expr_to_typed(state, rhs, env, span)?;
                match op {
                    SpecBinaryOp::Add => Ok(TypedExpr::Int(lhs.as_int()? + rhs.as_int()?)),
                    SpecBinaryOp::Sub => Ok(TypedExpr::Int(lhs.as_int()? - rhs.as_int()?)),
                    SpecBinaryOp::Mul => Ok(TypedExpr::Int(lhs.as_int()? * rhs.as_int()?)),
                    SpecBinaryOp::Eq => Ok(TypedExpr::Bool(lhs.eq(&rhs)?)),
                    SpecBinaryOp::Ne => Ok(TypedExpr::Bool(lhs.eq(&rhs)?.not())),
                    SpecBinaryOp::Gt => Ok(TypedExpr::Bool(lhs.as_int()?.gt(&rhs.as_int()?))),
                    SpecBinaryOp::Ge => Ok(TypedExpr::Bool(lhs.as_int()?.ge(&rhs.as_int()?))),
                    SpecBinaryOp::Lt => Ok(TypedExpr::Bool(lhs.as_int()?.lt(&rhs.as_int()?))),
                    SpecBinaryOp::Le => Ok(TypedExpr::Bool(lhs.as_int()?.le(&rhs.as_int()?))),
                    SpecBinaryOp::And => {
                        let lhs = lhs.as_bool()?;
                        let rhs = rhs.as_bool()?;
                        Ok(TypedExpr::Bool(Bool::and(&[&lhs, &rhs])))
                    }
                    SpecBinaryOp::Or => {
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

    fn ensure_formula(
        &self,
        state: &State,
        formula: Bool,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        self.solver.push();
        for cond in &state.pc {
            self.solver.assert(cond);
        }
        for cond in &state.assertion {
            self.solver.assert(cond);
        }
        self.solver.assert(formula.not());
        let result = match self.solver.check() {
            SatResult::Sat => {
                let model = self
                    .solver
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
        };
        self.solver.pop(1);
        result
    }

    fn place_ty(&self, place: Place<'tcx>) -> rustc_middle::ty::Ty<'tcx> {
        place.ty(&self.body, self.tcx).ty
    }

    fn place_is_copy(&self, place: Place<'tcx>) -> bool {
        self.ty_is_copy(self.place_ty(place))
    }

    fn ty_is_copy(&self, ty: rustc_middle::ty::Ty<'tcx>) -> bool {
        match ty.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) => true,
            TyKind::Tuple(fields) if fields.is_empty() => true,
            TyKind::Tuple(fields) => fields.iter().all(|field| self.ty_is_copy(field)),
            TyKind::Ref(_, _, rustc_middle::mir::Mutability::Not) => true,
            TyKind::Ref(_, _, rustc_middle::mir::Mutability::Mut) => false,
            _ => false,
        }
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

    fn initial_state(&self) -> Result<State, VerificationResult> {
        let mut state = State::empty();
        for local in self
            .body
            .local_decls
            .indices()
            .take(self.body.arg_count + 1)
        {
            let ty = self.body.local_decls[local].ty;
            let value =
                self.fresh_symval_for_ty(&mut state, ty, &format!("arg_{}", local.as_usize()))?;
            let loc = self.alloc(&mut state, value);
            state.env.insert(local, loc);
            state.live.insert(local, true);
        }

        if let Some(contract) = self.contracts.get(&self.def_id) {
            if contract.params.len() != self.body.arg_count {
                return Err(function_contract_error(
                    self.tcx,
                    self.def_id,
                    self.tcx.def_span(self.def_id),
                    format!(
                        "function contract parameter count mismatch: expected {}, found {}",
                        self.body.arg_count,
                        contract.params.len()
                    ),
                ));
            }
            let mut env = HashMap::new();
            for (name, local) in contract
                .params
                .iter()
                .cloned()
                .zip(self.body.local_decls.indices().skip(1))
            {
                let loc = state.env[&local];
                let value = state.store.get(&loc).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        None,
                        None,
                        format!("missing store for local {}", local.as_usize()),
                        Vec::new(),
                    )
                })?;
                if let Slot::Live(value) = value {
                    env.insert(name, value);
                }
            }
            let req = self.contract_expr_to_bool(
                &state,
                &contract.req,
                &env,
                self.tcx.def_span(self.def_id),
            )?;
            state.pc.push(req);
        }
        Ok(state)
    }

    fn alloc(&self, state: &mut State, value: SymVal) -> Loc {
        self.alloc_slot(state, Slot::Live(value))
    }

    fn alloc_slot(&self, state: &mut State, value: Slot) -> Loc {
        let loc = Loc(self.next_loc.get());
        self.next_loc.set(self.next_loc.get() + 1);
        state.store.insert(loc, value);
        loc
    }

    fn update_mutref_aliases(
        &self,
        state: &mut State,
        target: Loc,
        cur: Option<&SymVal>,
        fin: Option<&SymVal>,
    ) {
        let locs: Vec<_> = state.store.keys().copied().collect();
        for loc in locs {
            Self::update_mutref_aliases_at_loc(state, loc, target, cur, fin);
        }
    }

    fn update_mutref_aliases_at_loc(
        state: &mut State,
        loc: Loc,
        target: Loc,
        cur: Option<&SymVal>,
        fin: Option<&SymVal>,
    ) {
        let recurse = match state.store.get_mut(&loc) {
            Some(Slot::Live(SymVal::MutRef {
                target: slot_target,
                cur: slot_cur,
                fin: slot_fin,
            })) if *slot_target == target => {
                if let Some(cur) = cur {
                    **slot_cur = cur.clone();
                }
                if let Some(fin) = fin {
                    **slot_fin = fin.clone();
                }
                None
            }
            Some(Slot::Live(SymVal::Tuple(fields))) => Some(fields.to_vec()),
            _ => None,
        };
        if let Some(fields) = recurse {
            for loc in fields {
                Self::update_mutref_aliases_at_loc(state, loc, target, cur, fin);
            }
        }
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

    fn clone_slot_into_state(
        &self,
        state: &mut State,
        source_state: &State,
        slot: &Slot,
    ) -> Option<Slot> {
        match slot {
            Slot::Moved => Some(Slot::Moved),
            Slot::Live(value) => Some(Slot::Live(self.clone_symval_into_state(
                state,
                source_state,
                value,
            )?)),
        }
    }

    fn clone_symval_into_state(
        &self,
        state: &mut State,
        source_state: &State,
        value: &SymVal,
    ) -> Option<SymVal> {
        match value {
            SymVal::Scalar(expr) => Some(SymVal::Scalar(expr.clone())),
            SymVal::Tuple(fields) => {
                let mut locs = Vec::with_capacity(fields.len());
                for loc in fields.iter() {
                    let slot = self.clone_slot_into_state(
                        state,
                        source_state,
                        source_state.store.get(loc)?,
                    )?;
                    locs.push(self.alloc_slot(state, slot));
                }
                Some(SymVal::Tuple(locs.into_boxed_slice()))
            }
            SymVal::MutRef { target, cur, fin } => Some(SymVal::MutRef {
                target: *target,
                cur: Box::new(self.clone_symval_into_state(state, source_state, cur)?),
                fin: Box::new(self.clone_symval_into_state(state, source_state, fin)?),
            }),
        }
    }

    fn merge_slot(
        &self,
        merged: &mut State,
        guard: &Bool,
        existing_state: &State,
        existing: &Slot,
        incoming_state: &State,
        incoming: &Slot,
    ) -> Option<Slot> {
        match (existing, incoming) {
            (Slot::Moved, Slot::Moved) => Some(Slot::Moved),
            (Slot::Moved, Slot::Live(_)) | (Slot::Live(_), Slot::Moved) => Some(Slot::Moved),
            (Slot::Live(existing), Slot::Live(incoming)) => Some(Slot::Live(self.merge_symval(
                merged,
                guard,
                existing_state,
                existing,
                incoming_state,
                incoming,
            )?)),
        }
    }

    fn merge_symval(
        &self,
        merged: &mut State,
        guard: &Bool,
        existing_state: &State,
        existing: &SymVal,
        incoming_state: &State,
        incoming: &SymVal,
    ) -> Option<SymVal> {
        match (existing, incoming) {
            (SymVal::Scalar(existing), SymVal::Scalar(incoming)) => Some(SymVal::Scalar(
                self.merge_typed_expr(guard, existing, incoming)?,
            )),
            (SymVal::Tuple(existing_fields), SymVal::Tuple(incoming_fields)) => {
                if existing_fields.len() != incoming_fields.len() {
                    return None;
                }
                let mut locs = Vec::with_capacity(existing_fields.len());
                for (existing_loc, incoming_loc) in existing_fields
                    .iter()
                    .copied()
                    .zip(incoming_fields.iter().copied())
                {
                    let merged_slot = self.merge_slot(
                        merged,
                        guard,
                        existing_state,
                        existing_state.store.get(&existing_loc)?,
                        incoming_state,
                        incoming_state.store.get(&incoming_loc)?,
                    )?;
                    locs.push(self.alloc_slot(merged, merged_slot));
                }
                Some(SymVal::Tuple(locs.into_boxed_slice()))
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
                cur: Box::new(self.merge_symval(
                    merged,
                    guard,
                    existing_state,
                    existing_cur,
                    incoming_state,
                    incoming_cur,
                )?),
                fin: Box::new(self.merge_symval(
                    merged,
                    guard,
                    existing_state,
                    existing_fin,
                    incoming_state,
                    incoming_fin,
                )?),
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
            (TypedExpr::Tuple(existing_fields), TypedExpr::Tuple(incoming_fields)) => {
                if existing_fields.len() != incoming_fields.len() {
                    return None;
                }
                let mut fields = Vec::with_capacity(existing_fields.len());
                for (existing, incoming) in existing_fields.iter().zip(incoming_fields.iter()) {
                    fields.push(self.merge_typed_expr(guard, existing, incoming)?);
                }
                Some(TypedExpr::Tuple(fields.into_boxed_slice()))
            }
            _ => None,
        }
    }

    fn close_live_mut_refs(&self, state: &mut State, span: Span) -> Result<(), VerificationResult> {
        let return_local = Local::from_usize(0);
        let locals: Vec<_> = state
            .live
            .iter()
            .filter_map(|(local, live)| (*live && *local != return_local).then_some(*local))
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
        self.close_loc(state, loc, span)
    }

    fn close_loc(&self, state: &mut State, loc: Loc, span: Span) -> Result<(), VerificationResult> {
        let Some(mut value) = state.store.get(&loc).cloned() else {
            return Ok(());
        };
        self.close_slot(state, &mut value, span)?;
        state.store.insert(loc, value);
        Ok(())
    }

    fn close_slot(
        &self,
        state: &mut State,
        slot: &mut Slot,
        span: Span,
    ) -> Result<(), VerificationResult> {
        match slot {
            Slot::Moved => Ok(()),
            Slot::Live(value) => {
                if self.close_symval(state, value, span)? {
                    *slot = Slot::Moved;
                }
                Ok(())
            }
        }
    }

    fn close_symval(
        &self,
        state: &mut State,
        value: &mut SymVal,
        span: Span,
    ) -> Result<bool, VerificationResult> {
        match value {
            SymVal::MutRef { target, cur, fin } => {
                let formula = self.symval_eq(state, cur.as_ref(), fin.as_ref())?;
                self.ensure_formula(
                    state,
                    formula.clone(),
                    span,
                    "mutable reference close failed".to_owned(),
                )?;
                state.assertion.push(formula);
                state.store.insert(*target, Slot::Live((**cur).clone()));
                Ok(true)
            }
            SymVal::Tuple(fields) => {
                for loc in fields.iter().copied() {
                    self.close_loc(state, loc, span)?;
                }
                Ok(false)
            }
            SymVal::Scalar(_) => Ok(false),
        }
    }

    fn symval_eq(
        &self,
        state: &State,
        lhs: &SymVal,
        rhs: &SymVal,
    ) -> Result<Bool, VerificationResult> {
        match (lhs, rhs) {
            (SymVal::Scalar(lhs), SymVal::Scalar(rhs)) => lhs.eq(rhs),
            (SymVal::Tuple(lhs_fields), SymVal::Tuple(rhs_fields)) => {
                if lhs_fields.len() != rhs_fields.len() {
                    return Ok(Bool::from_bool(false));
                }
                if lhs_fields.is_empty() {
                    return Ok(Bool::from_bool(true));
                }
                let mut terms = Vec::with_capacity(lhs_fields.len());
                for (lhs_loc, rhs_loc) in lhs_fields.iter().copied().zip(rhs_fields.iter().copied())
                {
                    let lhs_slot = state.store.get(&lhs_loc).ok_or_else(|| {
                        self.unsupported_result(
                            self.tcx.def_span(self.def_id),
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "missing tuple field".to_owned(),
                            state.trace.clone(),
                        )
                    })?;
                    let rhs_slot = state.store.get(&rhs_loc).ok_or_else(|| {
                        self.unsupported_result(
                            self.tcx.def_span(self.def_id),
                            Some(state.ctrl.basic_block.index()),
                            Some(state.ctrl.statement_index),
                            "missing tuple field".to_owned(),
                            state.trace.clone(),
                        )
                    })?;
                    terms.push(self.slot_eq(state, lhs_slot, rhs_slot)?);
                }
                let refs: Vec<_> = terms.iter().collect();
                Ok(Bool::and(&refs))
            }
            (
                SymVal::MutRef {
                    target: lhs_target,
                    cur: lhs_cur,
                    fin: lhs_fin,
                },
                SymVal::MutRef {
                    target: rhs_target,
                    cur: rhs_cur,
                    fin: rhs_fin,
                },
            ) if lhs_target == rhs_target => {
                let cur = self.symval_eq(state, lhs_cur, rhs_cur)?;
                let fin = self.symval_eq(state, lhs_fin, rhs_fin)?;
                Ok(Bool::and(&[&cur, &fin]))
            }
            _ => Ok(Bool::from_bool(false)),
        }
    }

    fn slot_eq(&self, state: &State, lhs: &Slot, rhs: &Slot) -> Result<Bool, VerificationResult> {
        match (lhs, rhs) {
            (Slot::Moved, Slot::Moved) => Ok(Bool::from_bool(true)),
            (Slot::Live(lhs), Slot::Live(rhs)) => self.symval_eq(state, lhs, rhs),
            _ => Ok(Bool::from_bool(false)),
        }
    }
}

impl State {
    fn empty() -> Self {
        Self {
            env: BTreeMap::new(),
            store: BTreeMap::new(),
            pc: Vec::new(),
            assertion: Vec::new(),
            live: BTreeMap::new(),
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
            TypedExpr::Tuple(fields) if fields.is_empty() => Ok(Bool::from_bool(true)),
            TypedExpr::Tuple(_) => Err(VerificationResult {
                function: String::new(),
                status: VerificationStatus::Unsupported,
                span: String::new(),
                basic_block: None,
                statement_index: None,
                message: "expected boolean expression".to_owned(),
                trace: Vec::new(),
                model: Vec::new(),
            }),
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
            (TypedExpr::Tuple(lhs_fields), TypedExpr::Tuple(rhs_fields)) => {
                if lhs_fields.len() != rhs_fields.len() {
                    return Ok(Bool::from_bool(false));
                }
                if lhs_fields.is_empty() {
                    return Ok(Bool::from_bool(true));
                }
                let mut terms = Vec::with_capacity(lhs_fields.len());
                for (lhs, rhs) in lhs_fields.iter().zip(rhs_fields.iter()) {
                    terms.push(lhs.eq(rhs)?);
                }
                let refs: Vec<_> = terms.iter().collect();
                Ok(Bool::and(&refs))
            }
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

impl SymVal {
    fn to_typed_current(&self, state: &State, span: Span) -> Result<TypedExpr, VerificationResult> {
        match self {
            SymVal::Scalar(expr) => Ok(expr.clone()),
            SymVal::Tuple(fields) => {
                let mut typed = Vec::with_capacity(fields.len());
                for loc in fields.iter().copied() {
                    let Some(Slot::Live(value)) = state.store.get(&loc) else {
                        return Err(VerificationResult {
                            function: String::new(),
                            status: VerificationStatus::Unsupported,
                            span: String::new(),
                            basic_block: None,
                            statement_index: None,
                            message: format!("missing tuple field {loc:?}"),
                            trace: Vec::new(),
                            model: Vec::new(),
                        });
                    };
                    typed.push(value.to_typed_current(state, span)?);
                }
                Ok(TypedExpr::Tuple(typed.into_boxed_slice()))
            }
            SymVal::MutRef { cur, .. } => cur.to_typed_current(state, span),
        }
    }

    fn to_typed_prophecy(
        &self,
        state: &State,
        span: Span,
    ) -> Result<TypedExpr, VerificationResult> {
        match self {
            SymVal::Scalar(expr) => Ok(expr.clone()),
            SymVal::Tuple(fields) => {
                let mut typed = Vec::with_capacity(fields.len());
                for loc in fields.iter().copied() {
                    let Some(Slot::Live(value)) = state.store.get(&loc) else {
                        return Err(VerificationResult {
                            function: String::new(),
                            status: VerificationStatus::Unsupported,
                            span: String::new(),
                            basic_block: None,
                            statement_index: None,
                            message: format!("missing tuple field {loc:?}"),
                            trace: Vec::new(),
                            model: Vec::new(),
                        });
                    };
                    typed.push(value.to_typed_prophecy(state, span)?);
                }
                Ok(TypedExpr::Tuple(typed.into_boxed_slice()))
            }
            SymVal::MutRef { fin, .. } => fin.to_typed_prophecy(state, span),
        }
    }
}

impl Slot {
    fn take(&mut self) -> Option<SymVal> {
        match std::mem::replace(self, Slot::Moved) {
            Slot::Live(value) => Some(value),
            Slot::Moved => None,
        }
    }
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

fn collect_function_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<HashMap<LocalDefId, FunctionContract>, VerificationResult> {
    let mut contracts = HashMap::new();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let ItemKind::Fn { .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        if let Some(contract) = parse_function_contract(tcx, def_id, item.span)? {
            contracts.insert(def_id, contract);
        }
    }
    Ok(contracts)
}

fn parse_function_contract<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
) -> Result<Option<FunctionContract>, VerificationResult> {
    let loc = tcx.sess.source_map().lookup_char_pos(item_span.lo());
    let Some(source) = loc.file.src.as_deref() else {
        return Ok(None);
    };
    let lines: Vec<_> = source.lines().collect();
    if loc.line <= 1 {
        return Ok(None);
    }
    let mut idx = loc.line - 2;
    let mut block = Vec::new();
    while let Some(line) = lines.get(idx) {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            break;
        }
        if !trimmed.starts_with("//@") {
            break;
        }
        block.push(trimmed.to_owned());
        if idx == 0 {
            break;
        }
        idx -= 1;
    }
    block.reverse();

    let mut req = None;
    let mut ens = None;
    let mut saw_contract = false;
    for line in block {
        if let Some(rest) = line.strip_prefix("//@ req") {
            if req.is_some() {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    item_span,
                    "multiple //@ req directives for a function".to_owned(),
                ));
            }
            saw_contract = true;
            req = Some(parse_function_contract_expr(
                tcx,
                def_id,
                item_span,
                "req",
                rest.trim(),
            )?);
        } else if let Some(rest) = line.strip_prefix("//@ ens") {
            if ens.is_some() {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    item_span,
                    "multiple //@ ens directives for a function".to_owned(),
                ));
            }
            saw_contract = true;
            ens = Some(parse_function_contract_expr(
                tcx,
                def_id,
                item_span,
                "ens",
                rest.trim(),
            )?);
        }
    }

    if !saw_contract {
        return Ok(None);
    }

    let req = req.ok_or_else(|| {
        function_contract_error(
            tcx,
            def_id,
            item_span,
            "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        )
    })?;
    let ens = ens.ok_or_else(|| {
        function_contract_error(
            tcx,
            def_id,
            item_span,
            "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        )
    })?;
    Ok(Some(FunctionContract {
        params: function_param_names(tcx, def_id)?,
        req,
        ens,
    }))
}

fn parse_function_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: Span,
    kind: &str,
    text: &str,
) -> Result<ContractExpr, VerificationResult> {
    let lit = syn::parse_str::<LitStr>(text).map_err(|err| {
        function_contract_error(
            tcx,
            def_id,
            span,
            format!("failed to parse //@ {kind} predicate: {err}"),
        )
    })?;
    let expr = parse_spec_template(kind, &lit)
        .map_err(|err| function_contract_error(tcx, def_id, span, err.to_string()))?;
    lower_contract_expr(tcx, def_id, span, kind, &expr)
}

fn lower_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: Span,
    kind: &str,
    expr: &SynExpr,
) -> Result<ContractExpr, VerificationResult> {
    match expr {
        SynExpr::Lit(lit) => match &lit.lit {
            Lit::Bool(value) => Ok(ContractExpr::Bool(value.value)),
            Lit::Int(value) => Ok(ContractExpr::Int(value.base10_parse::<i64>().map_err(
                |err| {
                    function_contract_error(
                        tcx,
                        def_id,
                        span,
                        format!("integer literal in //@ {kind} is too large: {err}"),
                    )
                },
            )?)),
            _ => Err(function_contract_error(
                tcx,
                def_id,
                span,
                format!("unsupported literal in //@ {kind} predicate"),
            )),
        },
        SynExpr::Path(path) => {
            let Some(ident) = path.path.get_ident() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported path in //@ {kind} predicate"),
                ));
            };
            let name = ident.to_string();
            if name == "result" {
                return Ok(ContractExpr::Var(name));
            }
            Ok(ContractExpr::Var(name))
        }
        SynExpr::Call(expr) => {
            let SynExpr::Path(path) = expr.func.as_ref() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported call in //@ {kind} predicate"),
                ));
            };
            let Some(ident) = path.path.get_ident() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported call in //@ {kind} predicate"),
                ));
            };
            if ident != "__prophecy" || expr.args.len() != 1 {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported call in //@ {kind} predicate"),
                ));
            }
            let Some(SynExpr::Path(arg_path)) = expr.args.first() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported prophecy argument in //@ {kind} predicate"),
                ));
            };
            let Some(arg_ident) = arg_path.path.get_ident() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported prophecy argument in //@ {kind} predicate"),
                ));
            };
            Ok(ContractExpr::Prophecy(arg_ident.to_string()))
        }
        SynExpr::Unary(expr) => {
            let op = match expr.op {
                syn::UnOp::Not(_) => SpecUnaryOp::Not,
                syn::UnOp::Neg(_) => SpecUnaryOp::Neg,
                _ => {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        span,
                        format!("unsupported unary operator in //@ {kind} predicate"),
                    ));
                }
            };
            Ok(ContractExpr::Unary {
                op,
                arg: Box::new(lower_contract_expr(tcx, def_id, span, kind, &expr.expr)?),
            })
        }
        SynExpr::Binary(expr) => {
            let op = match expr.op {
                syn::BinOp::Add(_) => SpecBinaryOp::Add,
                syn::BinOp::Sub(_) => SpecBinaryOp::Sub,
                syn::BinOp::Mul(_) => SpecBinaryOp::Mul,
                syn::BinOp::Eq(_) => SpecBinaryOp::Eq,
                syn::BinOp::Ne(_) => SpecBinaryOp::Ne,
                syn::BinOp::Gt(_) => SpecBinaryOp::Gt,
                syn::BinOp::Ge(_) => SpecBinaryOp::Ge,
                syn::BinOp::Lt(_) => SpecBinaryOp::Lt,
                syn::BinOp::Le(_) => SpecBinaryOp::Le,
                syn::BinOp::And(_) => SpecBinaryOp::And,
                syn::BinOp::Or(_) => SpecBinaryOp::Or,
                _ => {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        span,
                        format!("unsupported binary operator in //@ {kind} predicate"),
                    ));
                }
            };
            Ok(ContractExpr::Binary {
                op,
                lhs: Box::new(lower_contract_expr(tcx, def_id, span, kind, &expr.left)?),
                rhs: Box::new(lower_contract_expr(tcx, def_id, span, kind, &expr.right)?),
            })
        }
        SynExpr::Paren(expr) => lower_contract_expr(tcx, def_id, span, kind, &expr.expr),
        SynExpr::Group(expr) => lower_contract_expr(tcx, def_id, span, kind, &expr.expr),
        SynExpr::Reference(expr) => lower_contract_expr(tcx, def_id, span, kind, &expr.expr),
        SynExpr::Cast(expr) => lower_contract_expr(tcx, def_id, span, kind, &expr.expr),
        _ => Err(function_contract_error(
            tcx,
            def_id,
            span,
            format!("unsupported expression in //@ {kind} predicate"),
        )),
    }
}

fn function_param_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Result<Vec<String>, VerificationResult> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut names = Vec::with_capacity(body.params.len());
    for (index, param) in body.params.iter().enumerate() {
        match param.pat.kind {
            PatKind::Binding(_, _, ident, _) => names.push(ident.name.to_string()),
            _ => {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    param.pat.span,
                    format!("unsupported function parameter pattern #{index}"),
                ));
            }
        }
    }
    Ok(names)
}

fn function_contract_error<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: Span,
    message: String,
) -> VerificationResult {
    VerificationResult {
        function: tcx.def_path_str(def_id.to_def_id()),
        status: VerificationStatus::Unsupported,
        span: span_text(tcx, span),
        basic_block: None,
        statement_index: None,
        message,
        trace: Vec::new(),
        model: Vec::new(),
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
        (TypedExpr::Tuple(left), TypedExpr::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right.iter())
                    .all(|(left, right)| same_typed_expr(left, right))
        }
        _ => false,
    }
}
