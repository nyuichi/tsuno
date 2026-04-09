#![allow(clippy::result_large_err)]

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::Once;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{
    AggregateKind, BasicBlock, BinOp, Body, BorrowKind, ConstOperand, Local, MutBorrowKind,
    Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use rustc_span::source_map::Spanned;
use z3::ast::{Ast, Bool, Int};
use z3::{SatResult, Solver, SortKind};

use crate::directive::{SpecBinaryOp, SpecUnaryOp};
use crate::prepass::{
    AssertionContracts, ContractExpr, FunctionContract, LoopContract, LoopContracts, MirSpecExpr,
    compute_assertions, compute_function_contracts, compute_loops,
};
use crate::report::{VerificationResult, VerificationStatus};

thread_local! {
    static GLOBAL_SOLVER: Solver = {
        init_z3();
        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);
        solver
    };
}

static Z3_INIT: Once = Once::new();

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ControlPoint {
    basic_block: BasicBlock,
    statement_index: usize,
}

#[derive(Debug, Clone)]
pub struct State {
    pc: Bool,
    assertion: Bool,
    model: BTreeMap<Local, SymVal>,
    ctrl: ControlPoint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SymTy {
    Bool,
    Int,
    Tuple(Box<[SymTy]>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SymVar {
    name: String,
    ty: SymTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymVal {
    Var(SymVar),
    Proj {
        base: Box<SymVal>,
        index: usize,
        ty: SymTy,
    },
    Int(i64),
    Bool(bool),
    Tuple(Box<[SymVal]>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum IntExpr {
    Value(SymVal),
    Add(Box<IntExpr>, Box<IntExpr>),
    Sub(Box<IntExpr>, Box<IntExpr>),
    Mul(Box<IntExpr>, Box<IntExpr>),
    Neg(Box<IntExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CmpOp {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BoolExpr {
    Const(bool),
    Value(SymVal),
    Cmp {
        op: CmpOp,
        lhs: IntExpr,
        rhs: IntExpr,
    },
    Eq(SymVal, SymVal),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Implies(Box<BoolExpr>, Box<BoolExpr>),
}

#[derive(Debug, Clone)]
struct EvaluatedRvalue {
    value: SymVal,
    constraints: Vec<BoolExpr>,
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: Body<'tcx>,
    contracts: HashMap<LocalDefId, FunctionContract>,
    loop_contracts: LoopContracts,
    assertion_contracts: AssertionContracts,
    prepass_error: Option<VerificationResult>,
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
                    message: error.message,
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
                        message: error.message,
                    });
                    AssertionContracts::empty()
                }
            }
        } else {
            AssertionContracts::empty()
        };
        let contracts = match compute_function_contracts(tcx) {
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
            contracts,
            loop_contracts,
            assertion_contracts,
            prepass_error,
            next_sym: Cell::new(0),
        }
    }

    pub fn verify(&self) -> VerificationResult {
        if let Some(result) = self.prepass_error.clone() {
            return result;
        }
        reset_solver();
        let initial_state = match self.initial_state() {
            Ok(state) => state,
            Err(err) => return err,
        };
        let mut pending: BTreeMap<ControlPoint, Vec<State>> = BTreeMap::new();
        let mut worklist = VecDeque::new();
        if let Some(err) = self.enqueue_state(&mut pending, &mut worklist, initial_state) {
            return err;
        }

        while let Some(ctrl) = worklist.pop_front() {
            let Some(bucket) = pending.remove(&ctrl) else {
                continue;
            };
            let state = match self.merge_bucket(bucket) {
                Ok(Some(state)) => state,
                Ok(None) => continue,
                Err(err) => return err,
            };
            let mut state = state;
            if let Some(assertion) = self
                .assertion_contracts
                .assertion_at(ctrl.basic_block, ctrl.statement_index)
            {
                let formula = match self.mir_spec_to_bool(&state, &assertion.assertion) {
                    Ok(formula) => formula,
                    Err(err) => return err,
                };
                let formula = match self.bool_expr_to_z3(&formula, self.control_span(ctrl)) {
                    Ok(formula) => formula,
                    Err(err) => return err,
                };
                if let Err(err) = self.require_constraint(
                    &mut state,
                    formula,
                    self.control_span(ctrl),
                    assertion.assertion_span.clone(),
                    "assertion failed".to_owned(),
                ) {
                    return err;
                }
            }

            let data = &self.body.basic_blocks[ctrl.basic_block];
            if ctrl.statement_index < data.statements.len() {
                let stmt = &data.statements[ctrl.statement_index];
                let next = match self.step_statement(state, stmt) {
                    Ok(next) => next,
                    Err(err) => return err,
                };
                if let Some(err) = self.enqueue_state(&mut pending, &mut worklist, next) {
                    return err;
                }
                continue;
            }

            let next_states = match self.step_terminator(state, data.terminator()) {
                Ok(next_states) => next_states,
                Err(err) => return err,
            };
            for next in next_states {
                if let Some(err) = self.enqueue_state(&mut pending, &mut worklist, next) {
                    return err;
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
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                let ty = self.body.local_decls[*local].ty;
                let value = self.fresh_for_rust_ty(ty, &format!("live_{}", local.as_usize()))?;
                state.model.insert(*local, value);
            }
            StatementKind::StorageDead(local) => {
                let ty = self.body.local_decls[*local].ty;
                if self.ty_contains_mut_ref(ty) {
                    self.resolve_and_remove_local(&mut state, *local, stmt.source_info.span)?;
                }
            }
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                let eval = self.eval_rvalue(&mut state, rvalue, stmt.source_info.span)?;
                self.write_place(&mut state, *place, eval.value, stmt.source_info.span)?;
                for constraint in eval.constraints {
                    let constraint = self.bool_expr_to_z3(&constraint, stmt.source_info.span)?;
                    self.assume_constraint(&mut state, constraint);
                }
            }
            StatementKind::Nop
            | StatementKind::Coverage(..)
            | StatementKind::FakeRead(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::ConstEvalCounter
            | StatementKind::PlaceMention(..) => {}
            other => {
                return Err(self.unsupported_result(
                    stmt.source_info.span,
                    format!("unsupported MIR statement {other:?}"),
                ));
            }
        }
        state.ctrl.statement_index += 1;
        Ok(state)
    }

    fn step_terminator(
        &self,
        mut state: State,
        term: &Terminator<'tcx>,
    ) -> Result<Vec<State>, VerificationResult> {
        match &term.kind {
            TerminatorKind::Goto { target } => {
                self.goto_target(state, *target, term.source_info.span)
            }
            TerminatorKind::Return => {
                if let Some(contract) = self.contracts.get(&self.def_id) {
                    let formula = self.contract_to_bool(&state, contract, true)?;
                    let formula = self.bool_expr_to_z3(&formula, term.source_info.span)?;
                    self.require_constraint(
                        &mut state,
                        formula,
                        term.source_info.span,
                        contract.ens_span.clone(),
                        "postcondition failed".to_owned(),
                    )?;
                }
                let live_locals: Vec<_> = state.model.keys().copied().collect();
                for local in live_locals {
                    if local != Local::from_usize(0) {
                        self.resolve_and_remove_local(&mut state, local, term.source_info.span)?;
                    }
                }
                Ok(Vec::new())
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_value = self.eval_operand(&mut state, discr, term.source_info.span)?;
                let mut next_states = Vec::new();
                let mut seen_conditions = Vec::new();
                for (value, target) in targets.iter() {
                    let branch = match discr.ty(&self.body, self.tcx).kind() {
                        TyKind::Bool => {
                            if value == 0 {
                                not_expr(self.symval_to_bool_expr(&discr_value)?)
                            } else {
                                self.symval_to_bool_expr(&discr_value)?
                            }
                        }
                        _ => BoolExpr::Cmp {
                            op: CmpOp::Eq,
                            lhs: self.symval_to_int_expr(&discr_value)?,
                            rhs: IntExpr::Value(SymVal::Int(value as i64)),
                        },
                    };
                    let branch = self.bool_expr_to_z3(&branch, term.source_info.span)?;
                    seen_conditions.push(branch.clone());
                    let mut next = state.clone();
                    next.pc = bool_and(vec![next.pc, branch]);
                    if let Some(loop_state) =
                        self.transition_to_block(next, target, term.source_info.span)?
                    {
                        next_states.push(loop_state);
                    }
                }
                let mut otherwise = state;
                otherwise.pc = bool_and(vec![otherwise.pc, bool_not(bool_or(seen_conditions))]);
                if let Some(loop_state) =
                    self.transition_to_block(otherwise, targets.otherwise(), term.source_info.span)?
                {
                    next_states.push(loop_state);
                }
                Ok(next_states)
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                msg,
                ..
            } => {
                let cond_value = self.eval_operand(&mut state, cond, term.source_info.span)?;
                let mut formula = self.symval_to_bool_expr(&cond_value)?;
                if !*expected {
                    formula = not_expr(formula);
                }
                let formula = self.bool_expr_to_z3(&formula, term.source_info.span)?;
                self.require_constraint(
                    &mut state,
                    formula,
                    term.source_info.span,
                    span_text(self.tcx, term.source_info.span),
                    format!("assertion failed: {msg:?}"),
                )?;
                self.goto_target(state, *target, term.source_info.span)
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
                format!("unsupported MIR terminator {other:?}"),
            )),
        }
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
        let callee = self.called_def_id(func);
        if let Some(def_id) = callee
            && let Some(contract) = self.contracts.get(&def_id)
        {
            let env = self.call_env(&mut state, args, contract, span)?;
            let req = self.contract_expr_to_bool(&env.current, &env.prophecy, &contract.req)?;
            let req = self.bool_expr_to_z3(&req, span)?;
            self.require_constraint(
                &mut state,
                req,
                span,
                contract.req_span.clone(),
                "precondition failed".to_owned(),
            )?;
            let result_ty = self.place_ty(destination);
            let result_value = self.fresh_for_rust_ty(result_ty, "call_result")?;
            self.write_place(&mut state, destination, result_value.clone(), span)?;
            self.abstract_call_mut_args(&mut state, args, span)?;
            let mut env = self.call_env(&mut state, args, contract, span)?;
            env.current.insert("result".to_owned(), result_value);
            let ens = self.contract_expr_to_bool(&env.current, &env.prophecy, &contract.ens)?;
            let ens = self.bool_expr_to_z3(&ens, span)?;
            self.assume_constraint(&mut state, ens);
        } else {
            let result_ty = self.place_ty(destination);
            let result_value = self.fresh_for_rust_ty(result_ty, "opaque_result")?;
            self.write_place(&mut state, destination, result_value, span)?;
            self.abstract_call_mut_args(&mut state, args, span)?;
        }
        let Some(target) = target else {
            return Ok(Vec::new());
        };
        self.goto_target(state, target, span)
    }

    fn goto_target(
        &self,
        state: State,
        target: BasicBlock,
        span: Span,
    ) -> Result<Vec<State>, VerificationResult> {
        Ok(match self.transition_to_block(state, target, span)? {
            Some(state) => vec![state],
            None => Vec::new(),
        })
    }

    fn transition_to_block(
        &self,
        mut state: State,
        target: BasicBlock,
        span: Span,
    ) -> Result<Option<State>, VerificationResult> {
        if let Some(loop_contract) = self.loop_contracts.contract_by_header(target) {
            let invariant = self.mir_spec_to_bool(&state, &loop_contract.invariant)?;
            let invariant = self.bool_expr_to_z3(&invariant, span)?;
            self.require_constraint(
                &mut state,
                invariant.clone(),
                span,
                loop_contract.invariant_span.clone(),
                "loop invariant does not hold".to_owned(),
            )?;
            if self.is_backedge(state.ctrl.basic_block, target, loop_contract) {
                if self.has_loop_marker(&state.pc, target) {
                    return Ok(None);
                }
                let mut abstract_state = state;
                self.havoc_loop_written_locals(&mut abstract_state, loop_contract)?;
                self.assume_constraint(&mut abstract_state, invariant);
                abstract_state.pc = bool_and(vec![abstract_state.pc, self.loop_marker(target)]);
                abstract_state.ctrl = ControlPoint {
                    basic_block: target,
                    statement_index: 0,
                };
                return Ok(Some(abstract_state));
            }
            self.assume_constraint(&mut state, invariant);
        }

        if let Some(header) = self.loop_contracts.header_for_invariant_block(target)
            && let Some(loop_contract) = self.loop_contracts.contract_by_header(header)
        {
            let invariant = self.mir_spec_to_bool(&state, &loop_contract.invariant)?;
            let invariant = self.bool_expr_to_z3(&invariant, span)?;
            self.assume_constraint(&mut state, invariant);
        }

        state.ctrl = ControlPoint {
            basic_block: target,
            statement_index: 0,
        };
        Ok(Some(state))
    }

    fn merge_bucket(&self, mut states: Vec<State>) -> Result<Option<State>, VerificationResult> {
        if states.is_empty() {
            return Ok(None);
        }
        if states.len() == 1 {
            return Ok(states.pop());
        }

        let shared: BTreeSet<_> = states
            .iter()
            .map(|state| state.model.keys().copied().collect::<BTreeSet<_>>())
            .reduce(|acc, keys| acc.intersection(&keys).copied().collect())
            .unwrap_or_default();

        for state in &mut states {
            let locals: Vec<_> = state.model.keys().copied().collect();
            for local in locals {
                if !shared.contains(&local) {
                    self.resolve_and_remove_local(state, local, self.control_span(state.ctrl))?;
                }
            }
        }

        let ctrl = states[0].ctrl;
        let mut merged = State {
            pc: Bool::from_bool(false),
            assertion: Bool::from_bool(true),
            model: BTreeMap::new(),
            ctrl,
        };
        let pcs = states
            .iter()
            .map(|state| state.pc.clone())
            .collect::<Vec<_>>();
        merged.pc = Bool::or(&pcs);

        let first_assertion = states
            .first()
            .map(|state| state.assertion.clone())
            .expect("non-empty states");
        if states
            .iter()
            .all(|state| state.assertion == first_assertion)
        {
            merged.assertion = first_assertion;
        } else {
            merged.assertion = bool_and(
                states
                    .iter()
                    .map(|state| state.pc.clone().implies(state.assertion.clone()))
                    .collect(),
            );
        }

        for local in shared {
            let ty = self.body.local_decls[local].ty;
            let mut incoming_values = states
                .iter()
                .map(|state| {
                    state
                        .model
                        .get(&local)
                        .cloned()
                        .expect("shared local present")
                })
                .collect::<Vec<_>>();
            let first_value = incoming_values
                .first()
                .cloned()
                .expect("shared local present");
            if incoming_values.iter().all(|value| *value == first_value) {
                merged.model.insert(local, first_value);
                continue;
            }

            let merged_value =
                self.fresh_for_rust_ty(ty, &format!("merge_{}", local.as_usize()))?;
            for (state, incoming) in states.iter().zip(incoming_values.drain(..)) {
                let equality =
                    self.sym_eq_to_z3(&merged_value, &incoming, self.control_span(ctrl))?;
                merged.assertion =
                    bool_and(vec![merged.assertion, state.pc.clone().implies(equality)]);
            }
            merged.model.insert(local, merged_value);
        }

        Ok(Some(merged))
    }

    fn enqueue_state(
        &self,
        pending: &mut BTreeMap<ControlPoint, Vec<State>>,
        worklist: &mut VecDeque<ControlPoint>,
        state: State,
    ) -> Option<VerificationResult> {
        match self.check_sat(
            std::slice::from_ref(&state.pc),
            self.control_span(state.ctrl),
            "solver returned unknown while checking path feasibility",
        ) {
            Ok(SatResult::Unsat) => None,
            Ok(SatResult::Sat) => {
                let ctrl = state.ctrl;
                let bucket = pending.entry(ctrl).or_default();
                if bucket.is_empty() {
                    worklist.push_back(ctrl);
                }
                bucket.push(state);
                None
            }
            Ok(SatResult::Unknown) => Some(self.unsupported_result(
                self.control_span(state.ctrl),
                "solver returned unknown while checking path feasibility".to_owned(),
            )),
            Err(err) => Some(err),
        }
    }

    fn initial_state(&self) -> Result<State, VerificationResult> {
        let mut state = State {
            pc: Bool::from_bool(true),
            assertion: Bool::from_bool(true),
            model: BTreeMap::new(),
            ctrl: ControlPoint {
                basic_block: BasicBlock::from_usize(0),
                statement_index: 0,
            },
        };
        for local in self
            .body
            .local_decls
            .indices()
            .take(self.body.arg_count + 1)
        {
            let ty = self.body.local_decls[local].ty;
            let value = self.fresh_for_rust_ty(ty, &format!("arg_{}", local.as_usize()))?;
            state.model.insert(local, value);
        }
        if let Some(contract) = self.contracts.get(&self.def_id) {
            let env = CallEnv::for_function(self, &state, contract)?;
            let req = self.contract_expr_to_bool(&env.current, &env.prophecy, &contract.req)?;
            let req = self.bool_expr_to_z3(&req, self.tcx.def_span(self.def_id))?;
            self.assume_constraint(&mut state, req);
        }
        Ok(state)
    }

    fn resolve_and_remove_local(
        &self,
        state: &mut State,
        local: Local,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let Some(value) = state.model.remove(&local) else {
            return Ok(());
        };
        let ty = self.body.local_decls[local].ty;
        let formulas = self.resolve_formulas(ty, &value, span)?;
        for formula in formulas {
            let formula = self.bool_expr_to_z3(&formula, span)?;
            self.require_constraint(
                state,
                formula,
                span,
                span_text(self.tcx, span),
                "mutable reference close failed".to_owned(),
            )?;
        }
        Ok(())
    }

    fn resolve_formulas(
        &self,
        ty: Ty<'tcx>,
        value: &SymVal,
        span: Span,
    ) -> Result<Vec<BoolExpr>, VerificationResult> {
        match ty.kind() {
            TyKind::Tuple(fields) => {
                let mut formulas = Vec::new();
                let field_tys: Vec<_> = fields.iter().collect();
                for (index, field_ty) in field_tys.into_iter().enumerate() {
                    let field_value = self.project_tuple_field(value.clone(), index, span)?;
                    formulas.extend(self.resolve_formulas(field_ty, &field_value, span)?);
                }
                Ok(formulas)
            }
            TyKind::Ref(_, inner, mutability) if mutability.is_mut() => {
                let SymVal::Tuple(parts) = value else {
                    return Err(self.unsupported_result(
                        span,
                        "mutable reference shape mismatch during resolve".to_owned(),
                    ));
                };
                if parts.len() != 2 {
                    return Err(self.unsupported_result(
                        span,
                        "mutable reference shape mismatch during resolve".to_owned(),
                    ));
                }
                let cur = parts[0].clone();
                let fin = parts[1].clone();
                if !matches!(inner.kind(), TyKind::Tuple(_)) {
                    return Ok(vec![BoolExpr::Eq(cur, fin)]);
                }
                Ok(vec![BoolExpr::Eq(cur, fin)])
            }
            TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Never => Ok(Vec::new()),
            other => Err(self.unsupported_result(span, format!("unsupported type {other:?}"))),
        }
    }

    fn eval_rvalue(
        &self,
        state: &mut State,
        rvalue: &Rvalue<'tcx>,
        span: Span,
    ) -> Result<EvaluatedRvalue, VerificationResult> {
        match rvalue {
            Rvalue::Use(operand) => Ok(EvaluatedRvalue {
                value: self.eval_operand(state, operand, span)?,
                constraints: Vec::new(),
            }),
            Rvalue::Ref(_, borrow_kind, place) => match borrow_kind {
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default | MutBorrowKind::TwoPhaseBorrow,
                } => self.create_mut_borrow(state, *place, span),
                _ => Err(self
                    .unsupported_result(span, format!("unsupported borrow kind {borrow_kind:?}"))),
            },
            Rvalue::BinaryOp(op, operands) => {
                self.eval_binary_op(state, *op, &operands.0, &operands.1, span)
            }
            Rvalue::UnaryOp(op, operand) => self.eval_unary_op(state, *op, operand, span),
            Rvalue::Aggregate(kind, operands) => match **kind {
                AggregateKind::Tuple => {
                    let mut values = Vec::with_capacity(operands.len());
                    for operand in operands {
                        values.push(self.eval_operand(state, operand, span)?);
                    }
                    Ok(EvaluatedRvalue {
                        value: SymVal::Tuple(values.into_boxed_slice()),
                        constraints: Vec::new(),
                    })
                }
                _ => Err(self.unsupported_result(span, format!("unsupported aggregate {kind:?}"))),
            },
            other => Err(self.unsupported_result(span, format!("unsupported rvalue {other:?}"))),
        }
    }

    fn create_mut_borrow(
        &self,
        state: &mut State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<EvaluatedRvalue, VerificationResult> {
        let current = self.read_place(state, place, ReadMode::Current, span)?;
        let final_value = if self.is_reborrow(place) {
            self.read_place(state, place, ReadMode::Final, span)?
        } else {
            let ty = self.place_ty(place);
            self.fresh_for_rust_ty(ty, "prophecy")?
        };
        self.write_place(state, place, final_value.clone(), span)?;
        Ok(EvaluatedRvalue {
            value: SymVal::Tuple(vec![current, final_value].into_boxed_slice()),
            constraints: Vec::new(),
        })
    }

    fn eval_binary_op(
        &self,
        state: &mut State,
        op: BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
        span: Span,
    ) -> Result<EvaluatedRvalue, VerificationResult> {
        let lhs_value = self.eval_operand(state, lhs, span)?;
        let rhs_value = self.eval_operand(state, rhs, span)?;
        match op {
            BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow => {
                self.eval_checked_binary_op(state, op, lhs, rhs, span)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let result =
                    self.fresh_for_rust_ty(lhs.ty(&self.body.local_decls, self.tcx), "binop")?;
                let lhs_term = self.symval_to_int_expr(&lhs_value)?;
                let rhs_term = self.symval_to_int_expr(&rhs_value)?;
                let term = match op {
                    BinOp::Add => IntExpr::Add(Box::new(lhs_term), Box::new(rhs_term)),
                    BinOp::Sub => IntExpr::Sub(Box::new(lhs_term), Box::new(rhs_term)),
                    BinOp::Mul => IntExpr::Mul(Box::new(lhs_term), Box::new(rhs_term)),
                    _ => unreachable!(),
                };
                Ok(EvaluatedRvalue {
                    value: result.clone(),
                    constraints: vec![BoolExpr::Cmp {
                        op: CmpOp::Eq,
                        lhs: self.symval_to_int_expr(&result)?,
                        rhs: term,
                    }],
                })
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let result = self.fresh_bool("cmp");
                let formula = match op {
                    BinOp::Eq => BoolExpr::Eq(lhs_value, rhs_value),
                    BinOp::Ne => not_expr(BoolExpr::Eq(lhs_value, rhs_value)),
                    BinOp::Lt => BoolExpr::Cmp {
                        op: CmpOp::Lt,
                        lhs: self.symval_to_int_expr(&lhs_value)?,
                        rhs: self.symval_to_int_expr(&rhs_value)?,
                    },
                    BinOp::Le => BoolExpr::Cmp {
                        op: CmpOp::Le,
                        lhs: self.symval_to_int_expr(&lhs_value)?,
                        rhs: self.symval_to_int_expr(&rhs_value)?,
                    },
                    BinOp::Gt => BoolExpr::Cmp {
                        op: CmpOp::Gt,
                        lhs: self.symval_to_int_expr(&lhs_value)?,
                        rhs: self.symval_to_int_expr(&rhs_value)?,
                    },
                    BinOp::Ge => BoolExpr::Cmp {
                        op: CmpOp::Ge,
                        lhs: self.symval_to_int_expr(&lhs_value)?,
                        rhs: self.symval_to_int_expr(&rhs_value)?,
                    },
                    _ => unreachable!(),
                };
                Ok(EvaluatedRvalue {
                    value: result.clone(),
                    constraints: vec![bool_assignment(result, formula)],
                })
            }
            other => {
                Err(self.unsupported_result(span, format!("unsupported binary operator {other:?}")))
            }
        }
    }

    fn eval_checked_binary_op(
        &self,
        state: &mut State,
        op: BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
        span: Span,
    ) -> Result<EvaluatedRvalue, VerificationResult> {
        let lhs_value = self.eval_operand(state, lhs, span)?;
        let rhs_value = self.eval_operand(state, rhs, span)?;
        let result_ty = lhs.ty(&self.body.local_decls, self.tcx);
        let result_value = self.fresh_for_rust_ty(result_ty, "checked")?;
        let overflow_value = self.fresh_bool("overflow");
        let lhs_term = self.symval_to_int_expr(&lhs_value)?;
        let rhs_term = self.symval_to_int_expr(&rhs_value)?;
        let math = match op {
            BinOp::Add | BinOp::AddWithOverflow => {
                IntExpr::Add(Box::new(lhs_term), Box::new(rhs_term))
            }
            BinOp::Sub | BinOp::SubWithOverflow => {
                IntExpr::Sub(Box::new(lhs_term), Box::new(rhs_term))
            }
            BinOp::Mul | BinOp::MulWithOverflow => {
                IntExpr::Mul(Box::new(lhs_term), Box::new(rhs_term))
            }
            other => {
                return Err(self.unsupported_result(
                    span,
                    format!("unsupported checked binary operator {other:?}"),
                ));
            }
        };
        let overflow = not_expr(self.in_range_formula(result_ty, math.clone(), span)?);
        Ok(EvaluatedRvalue {
            value: SymVal::Tuple(
                vec![result_value.clone(), overflow_value.clone()].into_boxed_slice(),
            ),
            constraints: vec![
                BoolExpr::Cmp {
                    op: CmpOp::Eq,
                    lhs: self.symval_to_int_expr(&result_value)?,
                    rhs: math,
                },
                bool_assignment(overflow_value, overflow),
            ],
        })
    }

    fn eval_unary_op(
        &self,
        state: &mut State,
        op: UnOp,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<EvaluatedRvalue, VerificationResult> {
        let value = self.eval_operand(state, operand, span)?;
        match op {
            UnOp::Not => {
                let result = self.fresh_bool("not");
                let formula = not_expr(self.symval_to_bool_expr(&value)?);
                Ok(EvaluatedRvalue {
                    value: result.clone(),
                    constraints: vec![bool_assignment(result, formula)],
                })
            }
            UnOp::Neg => {
                let result =
                    self.fresh_for_rust_ty(operand.ty(&self.body.local_decls, self.tcx), "neg")?;
                let term = IntExpr::Neg(Box::new(self.symval_to_int_expr(&value)?));
                Ok(EvaluatedRvalue {
                    value: result.clone(),
                    constraints: vec![BoolExpr::Cmp {
                        op: CmpOp::Eq,
                        lhs: self.symval_to_int_expr(&result)?,
                        rhs: term,
                    }],
                })
            }
            other => {
                Err(self.unsupported_result(span, format!("unsupported unary operator {other:?}")))
            }
        }
    }

    fn eval_operand(
        &self,
        state: &mut State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        match operand {
            Operand::Copy(place) => self.read_place(state, *place, ReadMode::Current, span),
            Operand::Move(place) => {
                let value = self.read_place(state, *place, ReadMode::Current, span)?;
                if place.projection.is_empty() {
                    state.model.remove(&place.local);
                } else {
                    self.dangle_place(state, *place, span)?;
                }
                Ok(value)
            }
            Operand::Constant(constant) => self.eval_const_operand(constant, span),
        }
    }

    fn eval_const_operand(
        &self,
        constant: &ConstOperand<'tcx>,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        let ty = constant.const_.ty();
        match ty.kind() {
            TyKind::Bool => {
                let value = constant
                    .const_
                    .try_eval_scalar_int(self.tcx, ty::TypingEnv::fully_monomorphized())
                    .ok_or_else(|| {
                        self.unsupported_result(
                            span,
                            "failed to evaluate boolean constant".to_owned(),
                        )
                    })?;
                Ok(SymVal::Bool(value.try_to_bool().map_err(|_| {
                    self.unsupported_result(span, "failed to evaluate boolean constant".to_owned())
                })?))
            }
            TyKind::Int(_) | TyKind::Uint(_) => {
                let value = constant
                    .const_
                    .try_eval_scalar_int(self.tcx, ty::TypingEnv::fully_monomorphized())
                    .ok_or_else(|| {
                        self.unsupported_result(
                            span,
                            "failed to evaluate integer constant".to_owned(),
                        )
                    })?;
                Ok(SymVal::Int(self.scalar_int_to_i64(ty, value, span)?))
            }
            TyKind::Tuple(fields) if fields.is_empty() => Ok(SymVal::Tuple(Box::new([]))),
            _ => Err(self.unsupported_result(span, format!("unsupported constant type {ty:?}"))),
        }
    }

    fn read_place(
        &self,
        state: &State,
        place: Place<'tcx>,
        mode: ReadMode,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        let Some(root) = state.model.get(&place.local).cloned() else {
            return Err(
                self.unsupported_result(span, format!("missing local {}", place.local.as_usize()))
            );
        };
        self.read_projection(root, place.as_ref().projection, mode, span)
    }

    fn read_projection(
        &self,
        value: SymVal,
        projection: &[PlaceElem<'tcx>],
        mode: ReadMode,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        if projection.is_empty() {
            return Ok(value);
        }
        match projection[0] {
            PlaceElem::Deref => {
                let SymVal::Tuple(parts) = value else {
                    return Err(self.unsupported_result(
                        span,
                        "deref of non-reference symbolic value".to_owned(),
                    ));
                };
                if parts.len() != 2 {
                    return Err(self
                        .unsupported_result(span, "mutable reference shape mismatch".to_owned()));
                }
                let next = match mode {
                    ReadMode::Current => parts[0].clone(),
                    ReadMode::Final => parts[1].clone(),
                };
                self.read_projection(next, &projection[1..], mode, span)
            }
            PlaceElem::Field(field, _) => {
                let next = self.project_tuple_field(value, field.index(), span)?;
                self.read_projection(next.clone(), &projection[1..], mode, span)
            }
            other => {
                Err(self
                    .unsupported_result(span, format!("unsupported place projection {other:?}")))
            }
        }
    }

    fn write_place(
        &self,
        state: &mut State,
        place: Place<'tcx>,
        value: SymVal,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let root = state
            .model
            .get(&place.local)
            .cloned()
            .unwrap_or_else(|| value.clone());
        let updated = self.write_projection(root, place.as_ref().projection, value, span)?;
        state.model.insert(place.local, updated);
        Ok(())
    }

    fn write_projection(
        &self,
        value: SymVal,
        projection: &[PlaceElem<'tcx>],
        replacement: SymVal,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        if projection.is_empty() {
            return Ok(replacement);
        }
        match projection[0] {
            PlaceElem::Deref => {
                let SymVal::Tuple(parts) = value else {
                    return Err(self.unsupported_result(
                        span,
                        "deref assignment on non-reference symbolic value".to_owned(),
                    ));
                };
                if parts.len() != 2 {
                    return Err(self
                        .unsupported_result(span, "mutable reference shape mismatch".to_owned()));
                }
                let mut items = parts.into_vec();
                items[0] =
                    self.write_projection(items[0].clone(), &projection[1..], replacement, span)?;
                Ok(SymVal::Tuple(items.into_boxed_slice()))
            }
            PlaceElem::Field(field, _) => {
                let field_types = match value.sym_ty() {
                    SymTy::Tuple(fields) => fields.into_vec(),
                    _ => {
                        return Err(self.unsupported_result(
                            span,
                            "field assignment on non-tuple symbolic value".to_owned(),
                        ));
                    }
                };
                let index = field.index();
                if index >= field_types.len() {
                    return Err(
                        self.unsupported_result(span, "tuple field out of range".to_owned())
                    );
                }
                let mut items = Vec::with_capacity(field_types.len());
                for (current_index, field_ty) in field_types.into_iter().enumerate() {
                    let field_value =
                        self.project_field(value.clone(), current_index, field_ty, span)?;
                    if current_index == index {
                        items.push(self.write_projection(
                            field_value,
                            &projection[1..],
                            replacement.clone(),
                            span,
                        )?);
                    } else {
                        items.push(field_value);
                    }
                }
                Ok(SymVal::Tuple(items.into_boxed_slice()))
            }
            other => Err(self
                .unsupported_result(span, format!("unsupported assignment projection {other:?}"))),
        }
    }

    fn dangle_place(
        &self,
        state: &mut State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let value = self.read_place(state, place, ReadMode::Current, span)?;
        let updated = self.dangle_value(self.place_ty(place), &value, span)?;
        self.write_place(state, place, updated, span)
    }

    fn dangle_value(
        &self,
        ty: Ty<'tcx>,
        value: &SymVal,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        match ty.kind() {
            TyKind::Tuple(fields) => {
                let mut updated = Vec::with_capacity(fields.len());
                for (index, field_ty) in fields.iter().enumerate() {
                    let field_value = self.project_tuple_field(value.clone(), index, span)?;
                    updated.push(self.dangle_value(field_ty, &field_value, span)?);
                }
                Ok(SymVal::Tuple(updated.into_boxed_slice()))
            }
            TyKind::Ref(_, inner, mutability) if mutability.is_mut() => {
                let SymVal::Tuple(parts) = value else {
                    return Err(self.unsupported_result(
                        span,
                        "reference shape mismatch during dangle".to_owned(),
                    ));
                };
                if parts.len() != 2 {
                    return Err(self.unsupported_result(
                        span,
                        "reference shape mismatch during dangle".to_owned(),
                    ));
                }
                let fresh = self.fresh_for_rust_ty(*inner, "dangle")?;
                Ok(SymVal::Tuple(
                    vec![fresh, parts[1].clone()].into_boxed_slice(),
                ))
            }
            TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) => Ok(value.clone()),
            other => {
                Err(self
                    .unsupported_result(span, format!("unsupported type {other:?} during dangle")))
            }
        }
    }

    fn mir_spec_to_bool(
        &self,
        state: &State,
        expr: &MirSpecExpr,
    ) -> Result<BoolExpr, VerificationResult> {
        match expr {
            MirSpecExpr::Bool(value) => Ok(BoolExpr::Const(*value)),
            MirSpecExpr::Int(_) => Err(self.unsupported_result(
                self.control_span(state.ctrl),
                "expected boolean spec expression".to_owned(),
            )),
            MirSpecExpr::Var(local) => {
                self.symval_to_bool_expr(state.model.get(local).ok_or_else(|| {
                    self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing local {}", local.as_usize()),
                    )
                })?)
            }
            MirSpecExpr::Prophecy(local) => {
                let value = self.local_prophecy(state, *local, self.control_span(state.ctrl))?;
                self.symval_to_bool_expr(&value)
            }
            MirSpecExpr::Unary { op, arg } => match op {
                SpecUnaryOp::Not => Ok(not_expr(self.mir_spec_to_bool(state, arg)?)),
                SpecUnaryOp::Neg => Err(self.unsupported_result(
                    self.control_span(state.ctrl),
                    "expected integer spec expression".to_owned(),
                )),
            },
            MirSpecExpr::Binary { op, lhs, rhs } => self.spec_binary_to_bool(state, *op, lhs, rhs),
        }
    }

    fn spec_binary_to_bool(
        &self,
        state: &State,
        op: SpecBinaryOp,
        lhs: &MirSpecExpr,
        rhs: &MirSpecExpr,
    ) -> Result<BoolExpr, VerificationResult> {
        match op {
            SpecBinaryOp::Eq => self.spec_eq_formula(state, lhs, rhs),
            SpecBinaryOp::Ne => Ok(not_expr(self.spec_eq_formula(state, lhs, rhs)?)),
            SpecBinaryOp::And => Ok(and_expr(vec![
                self.mir_spec_to_bool(state, lhs)?,
                self.mir_spec_to_bool(state, rhs)?,
            ])),
            SpecBinaryOp::Or => Ok(or_expr(vec![
                self.mir_spec_to_bool(state, lhs)?,
                self.mir_spec_to_bool(state, rhs)?,
            ])),
            SpecBinaryOp::Lt | SpecBinaryOp::Le | SpecBinaryOp::Gt | SpecBinaryOp::Ge => {
                Ok(BoolExpr::Cmp {
                    op: match op {
                        SpecBinaryOp::Lt => CmpOp::Lt,
                        SpecBinaryOp::Le => CmpOp::Le,
                        SpecBinaryOp::Gt => CmpOp::Gt,
                        SpecBinaryOp::Ge => CmpOp::Ge,
                        _ => unreachable!(),
                    },
                    lhs: self.mir_spec_to_int(state, lhs)?,
                    rhs: self.mir_spec_to_int(state, rhs)?,
                })
            }
            SpecBinaryOp::Add | SpecBinaryOp::Sub | SpecBinaryOp::Mul => Err(self
                .unsupported_result(
                    self.control_span(state.ctrl),
                    "expected boolean spec expression".to_owned(),
                )),
        }
    }

    fn mir_spec_to_int(
        &self,
        state: &State,
        expr: &MirSpecExpr,
    ) -> Result<IntExpr, VerificationResult> {
        match expr {
            MirSpecExpr::Int(value) => Ok(IntExpr::Value(SymVal::Int(*value))),
            MirSpecExpr::Var(local) => {
                self.symval_to_int_expr(state.model.get(local).ok_or_else(|| {
                    self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing local {}", local.as_usize()),
                    )
                })?)
            }
            MirSpecExpr::Prophecy(local) => {
                let value = self.local_prophecy(state, *local, self.control_span(state.ctrl))?;
                self.symval_to_int_expr(&value)
            }
            MirSpecExpr::Unary { op, arg } => match op {
                SpecUnaryOp::Neg => Ok(IntExpr::Neg(Box::new(self.mir_spec_to_int(state, arg)?))),
                SpecUnaryOp::Not => Err(self.unsupported_result(
                    self.control_span(state.ctrl),
                    "expected boolean spec expression".to_owned(),
                )),
            },
            MirSpecExpr::Binary { op, lhs, rhs } => match op {
                SpecBinaryOp::Add => Ok(IntExpr::Add(
                    Box::new(self.mir_spec_to_int(state, lhs)?),
                    Box::new(self.mir_spec_to_int(state, rhs)?),
                )),
                SpecBinaryOp::Sub => Ok(IntExpr::Sub(
                    Box::new(self.mir_spec_to_int(state, lhs)?),
                    Box::new(self.mir_spec_to_int(state, rhs)?),
                )),
                SpecBinaryOp::Mul => Ok(IntExpr::Mul(
                    Box::new(self.mir_spec_to_int(state, lhs)?),
                    Box::new(self.mir_spec_to_int(state, rhs)?),
                )),
                _ => Err(self.unsupported_result(
                    self.control_span(state.ctrl),
                    "expected integer spec expression".to_owned(),
                )),
            },
            MirSpecExpr::Bool(_) => Err(self.unsupported_result(
                self.control_span(state.ctrl),
                "expected integer spec expression".to_owned(),
            )),
        }
    }

    fn mir_spec_to_value(
        &self,
        state: &State,
        expr: &MirSpecExpr,
    ) -> Result<SymVal, VerificationResult> {
        match expr {
            MirSpecExpr::Bool(value) => Ok(SymVal::Bool(*value)),
            MirSpecExpr::Int(value) => Ok(SymVal::Int(*value)),
            MirSpecExpr::Var(local) => state.model.get(local).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.control_span(state.ctrl),
                    format!("missing local {}", local.as_usize()),
                )
            }),
            MirSpecExpr::Prophecy(local) => {
                self.local_prophecy(state, *local, self.control_span(state.ctrl))
            }
            MirSpecExpr::Unary { .. } | MirSpecExpr::Binary { .. } => Err(self.unsupported_result(
                self.control_span(state.ctrl),
                "complex spec values are unsupported outside comparisons".to_owned(),
            )),
        }
    }

    fn spec_eq_formula(
        &self,
        state: &State,
        lhs: &MirSpecExpr,
        rhs: &MirSpecExpr,
    ) -> Result<BoolExpr, VerificationResult> {
        if let (Ok(lhs), Ok(rhs)) = (
            self.mir_spec_to_int(state, lhs),
            self.mir_spec_to_int(state, rhs),
        ) {
            return Ok(BoolExpr::Cmp {
                op: CmpOp::Eq,
                lhs,
                rhs,
            });
        }
        Ok(BoolExpr::Eq(
            self.mir_spec_to_value(state, lhs)?,
            self.mir_spec_to_value(state, rhs)?,
        ))
    }

    fn contract_expr_to_bool(
        &self,
        current: &HashMap<String, SymVal>,
        prophecy: &HashMap<String, SymVal>,
        expr: &ContractExpr,
    ) -> Result<BoolExpr, VerificationResult> {
        match expr {
            ContractExpr::Bool(value) => Ok(BoolExpr::Const(*value)),
            ContractExpr::Int(_) => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                "expected boolean contract expression".to_owned(),
            )),
            ContractExpr::Var(name) => {
                self.symval_to_bool_expr(current.get(name).ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        format!("missing contract binding `{name}`"),
                    )
                })?)
            }
            ContractExpr::Prophecy(name) => {
                self.symval_to_bool_expr(prophecy.get(name).ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        format!("missing prophecy binding `{name}`"),
                    )
                })?)
            }
            ContractExpr::Unary { op, arg } => match op {
                SpecUnaryOp::Not => Ok(not_expr(
                    self.contract_expr_to_bool(current, prophecy, arg)?,
                )),
                SpecUnaryOp::Neg => Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "expected integer contract expression".to_owned(),
                )),
            },
            ContractExpr::Binary { op, lhs, rhs } => match op {
                SpecBinaryOp::Eq => self.contract_eq_formula(current, prophecy, lhs, rhs),
                SpecBinaryOp::Ne => Ok(not_expr(
                    self.contract_eq_formula(current, prophecy, lhs, rhs)?,
                )),
                SpecBinaryOp::And => Ok(and_expr(vec![
                    self.contract_expr_to_bool(current, prophecy, lhs)?,
                    self.contract_expr_to_bool(current, prophecy, rhs)?,
                ])),
                SpecBinaryOp::Or => Ok(or_expr(vec![
                    self.contract_expr_to_bool(current, prophecy, lhs)?,
                    self.contract_expr_to_bool(current, prophecy, rhs)?,
                ])),
                SpecBinaryOp::Lt | SpecBinaryOp::Le | SpecBinaryOp::Gt | SpecBinaryOp::Ge => {
                    Ok(BoolExpr::Cmp {
                        op: match op {
                            SpecBinaryOp::Lt => CmpOp::Lt,
                            SpecBinaryOp::Le => CmpOp::Le,
                            SpecBinaryOp::Gt => CmpOp::Gt,
                            SpecBinaryOp::Ge => CmpOp::Ge,
                            _ => unreachable!(),
                        },
                        lhs: self.contract_expr_to_int(current, prophecy, lhs)?,
                        rhs: self.contract_expr_to_int(current, prophecy, rhs)?,
                    })
                }
                SpecBinaryOp::Add | SpecBinaryOp::Sub | SpecBinaryOp::Mul => Err(self
                    .unsupported_result(
                        self.tcx.def_span(self.def_id),
                        "expected boolean contract expression".to_owned(),
                    )),
            },
        }
    }

    fn contract_expr_to_int(
        &self,
        current: &HashMap<String, SymVal>,
        prophecy: &HashMap<String, SymVal>,
        expr: &ContractExpr,
    ) -> Result<IntExpr, VerificationResult> {
        match expr {
            ContractExpr::Int(value) => Ok(IntExpr::Value(SymVal::Int(*value))),
            ContractExpr::Var(name) => {
                self.symval_to_int_expr(current.get(name).ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        format!("missing contract binding `{name}`"),
                    )
                })?)
            }
            ContractExpr::Prophecy(name) => {
                self.symval_to_int_expr(prophecy.get(name).ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        format!("missing prophecy binding `{name}`"),
                    )
                })?)
            }
            ContractExpr::Unary { op, arg } => match op {
                SpecUnaryOp::Neg => Ok(IntExpr::Neg(Box::new(
                    self.contract_expr_to_int(current, prophecy, arg)?,
                ))),
                SpecUnaryOp::Not => Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "expected boolean contract expression".to_owned(),
                )),
            },
            ContractExpr::Binary { op, lhs, rhs } => match op {
                SpecBinaryOp::Add => Ok(IntExpr::Add(
                    Box::new(self.contract_expr_to_int(current, prophecy, lhs)?),
                    Box::new(self.contract_expr_to_int(current, prophecy, rhs)?),
                )),
                SpecBinaryOp::Sub => Ok(IntExpr::Sub(
                    Box::new(self.contract_expr_to_int(current, prophecy, lhs)?),
                    Box::new(self.contract_expr_to_int(current, prophecy, rhs)?),
                )),
                SpecBinaryOp::Mul => Ok(IntExpr::Mul(
                    Box::new(self.contract_expr_to_int(current, prophecy, lhs)?),
                    Box::new(self.contract_expr_to_int(current, prophecy, rhs)?),
                )),
                _ => Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "expected integer contract expression".to_owned(),
                )),
            },
            ContractExpr::Bool(_) => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                "expected integer contract expression".to_owned(),
            )),
        }
    }

    fn contract_expr_to_value(
        &self,
        current: &HashMap<String, SymVal>,
        prophecy: &HashMap<String, SymVal>,
        expr: &ContractExpr,
    ) -> Result<SymVal, VerificationResult> {
        match expr {
            ContractExpr::Bool(value) => Ok(SymVal::Bool(*value)),
            ContractExpr::Int(value) => Ok(SymVal::Int(*value)),
            ContractExpr::Var(name) => current.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing contract binding `{name}`"),
                )
            }),
            ContractExpr::Prophecy(name) => prophecy.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing prophecy binding `{name}`"),
                )
            }),
            _ => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                "complex contract values are unsupported outside comparisons".to_owned(),
            )),
        }
    }

    fn contract_eq_formula(
        &self,
        current: &HashMap<String, SymVal>,
        prophecy: &HashMap<String, SymVal>,
        lhs: &ContractExpr,
        rhs: &ContractExpr,
    ) -> Result<BoolExpr, VerificationResult> {
        if let (Ok(lhs), Ok(rhs)) = (
            self.contract_expr_to_int(current, prophecy, lhs),
            self.contract_expr_to_int(current, prophecy, rhs),
        ) {
            return Ok(BoolExpr::Cmp {
                op: CmpOp::Eq,
                lhs,
                rhs,
            });
        }
        Ok(BoolExpr::Eq(
            self.contract_expr_to_value(current, prophecy, lhs)?,
            self.contract_expr_to_value(current, prophecy, rhs)?,
        ))
    }

    fn contract_to_bool(
        &self,
        state: &State,
        contract: &FunctionContract,
        include_result: bool,
    ) -> Result<BoolExpr, VerificationResult> {
        let env = CallEnv::for_function(self, state, contract)?;
        if include_result {
            self.contract_expr_to_bool(&env.current, &env.prophecy, &contract.ens)
        } else {
            self.contract_expr_to_bool(&env.current, &env.prophecy, &contract.req)
        }
    }

    fn require_constraint(
        &self,
        state: &mut State,
        constraint: Bool,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<(), VerificationResult> {
        self.assert_constraint(state, constraint);
        match self.check_sat(
            &[state.pc.clone(), state.assertion.clone()],
            span,
            "solver returned unknown while checking assertion",
        )? {
            SatResult::Sat => Ok(()),
            SatResult::Unsat => Err(VerificationResult {
                function: self.tcx.def_path_str(self.def_id.to_def_id()),
                status: VerificationStatus::Fail,
                span: diagnostic_span,
                message,
            }),
            SatResult::Unknown => Err(self.unsupported_result(
                span,
                "solver returned unknown while checking assertion".to_owned(),
            )),
        }
    }

    fn assume_constraint(&self, state: &mut State, constraint: Bool) {
        state.pc = bool_and(vec![state.pc.clone(), constraint]);
    }

    fn assert_constraint(&self, state: &mut State, constraint: Bool) {
        state.assertion = bool_and(vec![state.assertion.clone(), constraint]);
    }

    fn check_sat(
        &self,
        assumptions: &[Bool],
        span: Span,
        unknown_message: &str,
    ) -> Result<SatResult, VerificationResult> {
        with_solver(|solver| {
            let result = solver.check_assumptions(assumptions);
            if matches!(result, SatResult::Unknown) {
                return Err(self.unsupported_result(span, unknown_message.to_owned()));
            }
            Ok(result)
        })
    }

    fn bool_expr_to_z3(&self, expr: &BoolExpr, span: Span) -> Result<Bool, VerificationResult> {
        match expr {
            BoolExpr::Const(value) => Ok(Bool::from_bool(*value)),
            BoolExpr::Value(value) => self.symval_to_z3_bool(value, span),
            BoolExpr::Eq(lhs, rhs) => self.sym_eq_to_z3(lhs, rhs, span),
            BoolExpr::Cmp { op, lhs, rhs } => {
                let lhs = self.int_expr_to_z3(lhs, span)?;
                let rhs = self.int_expr_to_z3(rhs, span)?;
                Ok(match op {
                    CmpOp::Eq => lhs.eq(&rhs),
                    CmpOp::Lt => lhs.lt(&rhs),
                    CmpOp::Le => lhs.le(&rhs),
                    CmpOp::Gt => lhs.gt(&rhs),
                    CmpOp::Ge => lhs.ge(&rhs),
                })
            }
            BoolExpr::Not(arg) => Ok(self.bool_expr_to_z3(arg, span)?.not()),
            BoolExpr::And(args) => {
                let args = args
                    .iter()
                    .map(|arg| self.bool_expr_to_z3(arg, span))
                    .collect::<Result<Vec<_>, _>>()?;
                let refs = args.iter().collect::<Vec<_>>();
                Ok(Bool::and(&refs))
            }
            BoolExpr::Or(args) => {
                let args = args
                    .iter()
                    .map(|arg| self.bool_expr_to_z3(arg, span))
                    .collect::<Result<Vec<_>, _>>()?;
                let refs = args.iter().collect::<Vec<_>>();
                Ok(Bool::or(&refs))
            }
            BoolExpr::Implies(lhs, rhs) => Ok(self
                .bool_expr_to_z3(lhs, span)?
                .implies(self.bool_expr_to_z3(rhs, span)?)),
        }
    }

    fn int_expr_to_z3(&self, expr: &IntExpr, span: Span) -> Result<Int, VerificationResult> {
        match expr {
            IntExpr::Value(value) => self.symval_to_z3_int(value, span),
            IntExpr::Add(lhs, rhs) => {
                Ok(self.int_expr_to_z3(lhs, span)? + self.int_expr_to_z3(rhs, span)?)
            }
            IntExpr::Sub(lhs, rhs) => {
                Ok(self.int_expr_to_z3(lhs, span)? - self.int_expr_to_z3(rhs, span)?)
            }
            IntExpr::Mul(lhs, rhs) => {
                Ok(self.int_expr_to_z3(lhs, span)? * self.int_expr_to_z3(rhs, span)?)
            }
            IntExpr::Neg(arg) => Ok(Int::from_i64(0) - self.int_expr_to_z3(arg, span)?),
        }
    }

    fn symval_to_z3_bool(&self, value: &SymVal, span: Span) -> Result<Bool, VerificationResult> {
        match value {
            SymVal::Bool(value) => Ok(Bool::from_bool(*value)),
            SymVal::Var(var) if matches!(var.ty, SymTy::Bool) => {
                Ok(Bool::new_const(var.name.clone()))
            }
            SymVal::Proj {
                base,
                index,
                ty: SymTy::Bool,
            } => {
                let base_name = self.symval_name(base, span)?;
                Ok(Bool::new_const(format!("{base_name}.{index}")))
            }
            _ => Err(self.unsupported_result(span, "expected boolean symbolic value".to_owned())),
        }
    }

    fn symval_to_z3_int(&self, value: &SymVal, span: Span) -> Result<Int, VerificationResult> {
        match value {
            SymVal::Int(value) => Ok(Int::from_i64(*value)),
            SymVal::Var(var) if matches!(var.ty, SymTy::Int) => {
                Ok(Int::new_const(var.name.clone()))
            }
            SymVal::Proj {
                base,
                index,
                ty: SymTy::Int,
            } => {
                let base_name = self.symval_name(base, span)?;
                Ok(Int::new_const(format!("{base_name}.{index}")))
            }
            _ => Err(self.unsupported_result(span, "expected integer symbolic value".to_owned())),
        }
    }

    fn sym_eq_to_z3(
        &self,
        lhs: &SymVal,
        rhs: &SymVal,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match lhs.sym_ty() {
            SymTy::Tuple(fields) => {
                let mut parts = Vec::with_capacity(fields.len());
                for index in 0..fields.len() {
                    let lhs_field = self.project_tuple_field(lhs.clone(), index, span)?;
                    let rhs_field = self.project_tuple_field(rhs.clone(), index, span)?;
                    parts.push(self.sym_eq_to_z3(&lhs_field, &rhs_field, span)?);
                }
                let refs = parts.iter().collect::<Vec<_>>();
                Ok(Bool::and(&refs))
            }
            SymTy::Bool => Ok(self
                .symval_to_z3_bool(lhs, span)?
                .eq(self.symval_to_z3_bool(rhs, span)?)),
            SymTy::Int => Ok(self
                .symval_to_z3_int(lhs, span)?
                .eq(self.symval_to_z3_int(rhs, span)?)),
        }
    }

    fn symval_name(&self, value: &SymVal, span: Span) -> Result<String, VerificationResult> {
        match value {
            SymVal::Var(var) => Ok(var.name.clone()),
            SymVal::Proj { base, index, .. } => {
                Ok(format!("{}.{}", self.symval_name(base, span)?, index))
            }
            _ => Err(self.unsupported_result(span, "expected symbolic variable".to_owned())),
        }
    }

    fn symval_to_bool_expr(&self, value: &SymVal) -> Result<BoolExpr, VerificationResult> {
        match value {
            SymVal::Bool(value) => Ok(BoolExpr::Const(*value)),
            SymVal::Var(var) if matches!(var.ty, SymTy::Bool) => {
                Ok(BoolExpr::Value(SymVal::Var(var.clone())))
            }
            SymVal::Proj {
                ty: SymTy::Bool, ..
            } => Ok(BoolExpr::Value(value.clone())),
            _ => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                "expected boolean symbolic value".to_owned(),
            )),
        }
    }

    fn symval_to_int_expr(&self, value: &SymVal) -> Result<IntExpr, VerificationResult> {
        match value {
            SymVal::Int(value) => Ok(IntExpr::Value(SymVal::Int(*value))),
            SymVal::Var(var) if matches!(var.ty, SymTy::Int) => {
                Ok(IntExpr::Value(SymVal::Var(var.clone())))
            }
            SymVal::Proj { ty: SymTy::Int, .. } => Ok(IntExpr::Value(value.clone())),
            _ => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                "expected integer symbolic value".to_owned(),
            )),
        }
    }

    fn local_prophecy(
        &self,
        state: &State,
        local: Local,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        let value = state.model.get(&local).cloned().ok_or_else(|| {
            self.unsupported_result(span, format!("missing local {}", local.as_usize()))
        })?;
        let ty = self.body.local_decls[local].ty;
        match ty.kind() {
            TyKind::Ref(_, _, mutability) if mutability.is_mut() => {
                let SymVal::Tuple(parts) = value else {
                    return Err(self
                        .unsupported_result(span, "mutable reference shape mismatch".to_owned()));
                };
                Ok(parts[1].clone())
            }
            _ => Ok(value),
        }
    }

    fn abstract_call_mut_args(
        &self,
        state: &mut State,
        args: &[Spanned<Operand<'tcx>>],
        span: Span,
    ) -> Result<(), VerificationResult> {
        for arg in args {
            let place = match arg.node {
                Operand::Copy(place) | Operand::Move(place) => place,
                Operand::Constant(_) => continue,
            };
            let ty = self.place_ty(place);
            if matches!(ty.kind(), TyKind::Ref(_, _, mutability) if mutability.is_mut()) {
                let current = self.read_place(state, place, ReadMode::Current, span)?;
                let updated = self.abstract_mut_ref(&current, span)?;
                self.write_place(state, place, updated, span)?;
            }
        }
        Ok(())
    }

    fn abstract_mut_ref(&self, value: &SymVal, span: Span) -> Result<SymVal, VerificationResult> {
        let SymVal::Tuple(parts) = value else {
            return Err(
                self.unsupported_result(span, "mutable reference shape mismatch".to_owned())
            );
        };
        if parts.len() != 2 {
            return Err(
                self.unsupported_result(span, "mutable reference shape mismatch".to_owned())
            );
        }
        let fresh = self.fresh_for_symty(&parts[1].sym_ty(), "opaque_cur")?;
        Ok(SymVal::Tuple(
            vec![fresh, parts[1].clone()].into_boxed_slice(),
        ))
    }

    fn havoc_loop_written_locals(
        &self,
        state: &mut State,
        loop_contract: &LoopContract,
    ) -> Result<(), VerificationResult> {
        for local in &loop_contract.written_locals {
            if !state.model.contains_key(local) {
                continue;
            }
            let ty = self.body.local_decls[*local].ty;
            let fresh = self.fresh_for_rust_ty(ty, &format!("loop_{}", local.as_usize()))?;
            state.model.insert(*local, fresh);
        }
        Ok(())
    }

    fn is_backedge(
        &self,
        source: BasicBlock,
        target: BasicBlock,
        loop_contract: &LoopContract,
    ) -> bool {
        target == loop_contract.header && loop_contract.body_blocks.contains(&source)
    }

    fn loop_marker(&self, header: BasicBlock) -> Bool {
        Bool::new_const(format!("loop_{}", header.index()))
    }

    fn has_loop_marker(&self, expr: &Bool, header: BasicBlock) -> bool {
        let marker = format!("loop_{}", header.index());
        if expr.is_const() {
            return expr.decl().name() == marker;
        }
        expr.children().into_iter().any(|child| {
            child
                .as_bool()
                .filter(|_| child.sort_kind() == SortKind::Bool)
                .map(|child| self.has_loop_marker(&child, header))
                .unwrap_or(false)
        })
    }

    fn called_def_id(&self, func: &Operand<'tcx>) -> Option<LocalDefId> {
        let Operand::Constant(constant) = func else {
            return None;
        };
        let TyKind::FnDef(def_id, _) = *constant.const_.ty().kind() else {
            return None;
        };
        def_id.as_local()
    }

    fn place_ty(&self, place: Place<'tcx>) -> Ty<'tcx> {
        place.ty(&self.body.local_decls, self.tcx).ty
    }

    fn is_reborrow(&self, place: Place<'tcx>) -> bool {
        place
            .as_ref()
            .projection
            .iter()
            .any(|elem| matches!(elem, PlaceElem::Deref))
    }

    fn control_span(&self, ctrl: ControlPoint) -> Span {
        let data = &self.body.basic_blocks[ctrl.basic_block];
        if ctrl.statement_index < data.statements.len() {
            data.statements[ctrl.statement_index].source_info.span
        } else {
            data.terminator().source_info.span
        }
    }

    fn fresh_for_rust_ty(&self, ty: Ty<'tcx>, hint: &str) -> Result<SymVal, VerificationResult> {
        if let TyKind::Ref(_, inner, mutability) = ty.kind()
            && mutability.is_mut()
        {
            let current = self.fresh_for_rust_ty(*inner, &format!("{hint}_cur"))?;
            let final_value = self.fresh_for_rust_ty(*inner, &format!("{hint}_fin"))?;
            return Ok(SymVal::Tuple(vec![current, final_value].into_boxed_slice()));
        }
        let sym_ty = self.sym_ty_from_rust_ty(ty, self.tcx.def_span(self.def_id))?;
        self.fresh_for_symty(&sym_ty, hint)
    }

    fn fresh_for_symty(&self, ty: &SymTy, hint: &str) -> Result<SymVal, VerificationResult> {
        Ok(match ty {
            SymTy::Bool => self.fresh_bool(hint),
            SymTy::Int => self.fresh_int(hint),
            SymTy::Tuple(_) => SymVal::Var(SymVar {
                name: self.fresh_name(hint),
                ty: ty.clone(),
            }),
        })
    }

    fn project_tuple_field(
        &self,
        value: SymVal,
        index: usize,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        let ty = match value.sym_ty() {
            SymTy::Tuple(fields) => fields.get(index).cloned().ok_or_else(|| {
                self.unsupported_result(span, "tuple field out of range".to_owned())
            })?,
            _ => {
                return Err(self.unsupported_result(
                    span,
                    "field projection on non-tuple symbolic value".to_owned(),
                ));
            }
        };
        self.project_field(value, index, ty, span)
    }

    fn project_field(
        &self,
        value: SymVal,
        index: usize,
        ty: SymTy,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        match value {
            SymVal::Tuple(parts) => parts.get(index).cloned().ok_or_else(|| {
                self.unsupported_result(span, "tuple field out of range".to_owned())
            }),
            other => Ok(SymVal::Proj {
                base: Box::new(other),
                index,
                ty,
            }),
        }
    }

    fn fresh_bool(&self, hint: &str) -> SymVal {
        SymVal::Var(SymVar {
            name: self.fresh_name(hint),
            ty: SymTy::Bool,
        })
    }

    fn fresh_int(&self, hint: &str) -> SymVal {
        SymVal::Var(SymVar {
            name: self.fresh_name(hint),
            ty: SymTy::Int,
        })
    }

    fn fresh_name(&self, hint: &str) -> String {
        let id = self.next_sym.get();
        self.next_sym.set(id + 1);
        format!("{hint}_{id}")
    }

    fn sym_ty_from_rust_ty(&self, ty: Ty<'tcx>, span: Span) -> Result<SymTy, VerificationResult> {
        match ty.kind() {
            TyKind::Bool => Ok(SymTy::Bool),
            TyKind::Int(_) | TyKind::Uint(_) => Ok(SymTy::Int),
            TyKind::Tuple(fields) => {
                let mut items = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    items.push(self.sym_ty_from_rust_ty(field, span)?);
                }
                Ok(SymTy::Tuple(items.into_boxed_slice()))
            }
            TyKind::Ref(_, inner, mutability) if mutability.is_mut() => {
                let inner = self.sym_ty_from_rust_ty(*inner, span)?;
                Ok(SymTy::Tuple(vec![inner.clone(), inner].into_boxed_slice()))
            }
            other => Err(self.unsupported_result(span, format!("unsupported type {other:?}"))),
        }
    }

    fn ty_contains_mut_ref(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            TyKind::Ref(_, _, mutability) if mutability.is_mut() => true,
            TyKind::Tuple(fields) => fields.iter().any(|field| self.ty_contains_mut_ref(field)),
            _ => false,
        }
    }

    fn in_range_formula(
        &self,
        ty: Ty<'tcx>,
        value: IntExpr,
        span: Span,
    ) -> Result<BoolExpr, VerificationResult> {
        let bounds =
            match ty.kind() {
                TyKind::Int(kind) => match kind {
                    ty::IntTy::I8 => (-128_i64, 127_i64),
                    ty::IntTy::I16 => (-32768_i64, 32767_i64),
                    ty::IntTy::I32 => (i32::MIN as i64, i32::MAX as i64),
                    ty::IntTy::I64 => (i64::MIN, i64::MAX),
                    ty::IntTy::Isize => (i64::MIN, i64::MAX),
                    _ => {
                        return Err(self
                            .unsupported_result(span, format!("unsupported integer type {ty:?}")));
                    }
                },
                TyKind::Uint(kind) => match kind {
                    ty::UintTy::U8 => (0_i64, u8::MAX as i64),
                    ty::UintTy::U16 => (0_i64, u16::MAX as i64),
                    ty::UintTy::U32 => (0_i64, u32::MAX as i64),
                    ty::UintTy::U64 => (0_i64, i64::MAX),
                    ty::UintTy::Usize => (0_i64, i64::MAX),
                    _ => {
                        return Err(self
                            .unsupported_result(span, format!("unsupported integer type {ty:?}")));
                    }
                },
                _ => {
                    return Err(self
                        .unsupported_result(span, format!("expected integer type, found {ty:?}")));
                }
            };
        Ok(and_expr(vec![
            BoolExpr::Cmp {
                op: CmpOp::Ge,
                lhs: value.clone(),
                rhs: IntExpr::Value(SymVal::Int(bounds.0)),
            },
            BoolExpr::Cmp {
                op: CmpOp::Le,
                lhs: value,
                rhs: IntExpr::Value(SymVal::Int(bounds.1)),
            },
        ]))
    }

    fn scalar_int_to_i64(
        &self,
        ty: Ty<'tcx>,
        value: ty::ScalarInt,
        span: Span,
    ) -> Result<i64, VerificationResult> {
        match ty.kind() {
            TyKind::Int(kind) => Ok(match kind {
                ty::IntTy::I8 => value.to_i8().into(),
                ty::IntTy::I16 => value.to_i16().into(),
                ty::IntTy::I32 => value.to_i32().into(),
                ty::IntTy::I64 => value.to_i64(),
                ty::IntTy::Isize => value.to_i64(),
                _ => {
                    return Err(
                        self.unsupported_result(span, format!("unsupported integer type {ty:?}"))
                    );
                }
            }),
            TyKind::Uint(kind) => Ok(match kind {
                ty::UintTy::U8 => value.to_u8().into(),
                ty::UintTy::U16 => value.to_u16().into(),
                ty::UintTy::U32 => value.to_u32().into(),
                ty::UintTy::U64 => value.to_u64() as i64,
                ty::UintTy::Usize => value.to_u64() as i64,
                _ => {
                    return Err(
                        self.unsupported_result(span, format!("unsupported integer type {ty:?}"))
                    );
                }
            }),
            _ => Err(self.unsupported_result(span, format!("expected integer type, found {ty:?}"))),
        }
    }

    fn unsupported_result(&self, span: Span, message: String) -> VerificationResult {
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: VerificationStatus::Unsupported,
            span: span_text(self.tcx, span),
            message,
        }
    }

    fn pass_result(&self, message: &str) -> VerificationResult {
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: VerificationStatus::Pass,
            span: span_text(self.tcx, self.tcx.def_span(self.def_id)),
            message: message.to_owned(),
        }
    }

    fn call_env(
        &self,
        state: &mut State,
        args: &[Spanned<Operand<'tcx>>],
        contract: &FunctionContract,
        span: Span,
    ) -> Result<CallEnv, VerificationResult> {
        let mut current = HashMap::new();
        let mut prophecy = HashMap::new();
        if contract.params.len() != args.len() {
            return Err(self.unsupported_result(
                span,
                format!(
                    "call contract parameter count mismatch: expected {}, found {}",
                    contract.params.len(),
                    args.len()
                ),
            ));
        }
        for (name, arg) in contract.params.iter().zip(args.iter()) {
            let value = self.eval_operand(state, &arg.node, span)?;
            let ty = arg.node.ty(&self.body.local_decls, self.tcx);
            current.insert(name.clone(), value.clone());
            prophecy.insert(
                name.clone(),
                self.prophecy_from_typed_value(ty, &value, span)?,
            );
        }
        Ok(CallEnv { current, prophecy })
    }

    fn prophecy_from_typed_value(
        &self,
        ty: Ty<'tcx>,
        value: &SymVal,
        span: Span,
    ) -> Result<SymVal, VerificationResult> {
        match ty.kind() {
            TyKind::Ref(_, _, mutability) if mutability.is_mut() => {
                let SymVal::Tuple(parts) = value else {
                    return Err(self
                        .unsupported_result(span, "mutable reference shape mismatch".to_owned()));
                };
                if parts.len() != 2 {
                    return Err(self
                        .unsupported_result(span, "mutable reference shape mismatch".to_owned()));
                }
                Ok(parts[1].clone())
            }
            _ => Ok(value.clone()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ReadMode {
    Current,
    Final,
}

#[derive(Debug, Clone)]
struct CallEnv {
    current: HashMap<String, SymVal>,
    prophecy: HashMap<String, SymVal>,
}

impl CallEnv {
    fn for_function<'tcx>(
        verifier: &Verifier<'tcx>,
        state: &State,
        contract: &FunctionContract,
    ) -> Result<Self, VerificationResult> {
        let mut current = HashMap::new();
        let mut prophecy = HashMap::new();
        for (name, local) in contract
            .params
            .iter()
            .cloned()
            .zip(verifier.body.local_decls.indices().skip(1))
        {
            let value = state.model.get(&local).cloned().ok_or_else(|| {
                verifier.unsupported_result(
                    verifier.control_span(state.ctrl),
                    format!("missing local {}", local.as_usize()),
                )
            })?;
            prophecy.insert(
                name.clone(),
                verifier.prophecy_from_typed_value(
                    verifier.body.local_decls[local].ty,
                    &value,
                    verifier.control_span(state.ctrl),
                )?,
            );
            current.insert(name, value);
        }
        if let Some(result) = state.model.get(&Local::from_usize(0)).cloned() {
            current.insert("result".to_owned(), result);
        }
        Ok(Self { current, prophecy })
    }
}

impl SymVal {
    fn sym_ty(&self) -> SymTy {
        match self {
            SymVal::Var(var) => var.ty.clone(),
            SymVal::Proj { ty, .. } => ty.clone(),
            SymVal::Int(_) => SymTy::Int,
            SymVal::Bool(_) => SymTy::Bool,
            SymVal::Tuple(items) => SymTy::Tuple(
                items
                    .iter()
                    .map(SymVal::sym_ty)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            ),
        }
    }
}

fn init_z3() {
    Z3_INIT.call_once(|| {
        z3::set_global_param("model", "true");
    });
}

fn reset_solver() {
    with_solver(|solver| {
        solver.reset();
    });
}

fn with_solver<T>(f: impl FnOnce(&Solver) -> T) -> T {
    GLOBAL_SOLVER.with(|solver| f(solver))
}

fn and_expr(exprs: Vec<BoolExpr>) -> BoolExpr {
    let mut flat = Vec::new();
    for expr in exprs {
        match expr {
            BoolExpr::Const(true) => {}
            BoolExpr::Const(false) => return BoolExpr::Const(false),
            BoolExpr::And(items) => flat.extend(items),
            other => flat.push(other),
        }
    }
    match flat.len() {
        0 => BoolExpr::Const(true),
        1 => flat.pop().unwrap(),
        _ => BoolExpr::And(flat),
    }
}

fn or_expr(exprs: Vec<BoolExpr>) -> BoolExpr {
    let mut flat = Vec::new();
    for expr in exprs {
        match expr {
            BoolExpr::Const(false) => {}
            BoolExpr::Const(true) => return BoolExpr::Const(true),
            BoolExpr::Or(items) => flat.extend(items),
            other => flat.push(other),
        }
    }
    match flat.len() {
        0 => BoolExpr::Const(false),
        1 => flat.pop().unwrap(),
        _ => BoolExpr::Or(flat),
    }
}

fn bool_and(exprs: Vec<Bool>) -> Bool {
    match exprs.len() {
        0 => Bool::from_bool(true),
        1 => exprs.into_iter().next().unwrap(),
        _ => Bool::and(&exprs),
    }
}

fn bool_or(exprs: Vec<Bool>) -> Bool {
    match exprs.len() {
        0 => Bool::from_bool(false),
        1 => exprs.into_iter().next().unwrap(),
        _ => Bool::or(&exprs),
    }
}

fn bool_not(expr: Bool) -> Bool {
    expr.not()
}

fn not_expr(expr: BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Const(value) => BoolExpr::Const(!value),
        BoolExpr::Not(inner) => *inner,
        other => BoolExpr::Not(Box::new(other)),
    }
}

fn implies_expr(lhs: BoolExpr, rhs: BoolExpr) -> BoolExpr {
    BoolExpr::Implies(Box::new(lhs), Box::new(rhs))
}

fn bool_assignment(lhs: SymVal, rhs: BoolExpr) -> BoolExpr {
    let lhs_bool = BoolExpr::Value(lhs);
    and_expr(vec![
        implies_expr(lhs_bool.clone(), rhs.clone()),
        implies_expr(rhs, lhs_bool),
    ])
}

fn span_text(tcx: TyCtxt<'_>, span: Span) -> String {
    tcx.sess.source_map().span_to_diagnostic_string(span)
}
