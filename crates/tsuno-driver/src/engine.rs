#![allow(clippy::result_large_err)]

// Supported Rust types are reflected into the spec language and encoded in Z3 as follows:
//
// | Rust type                          | spec type           | Z3 representation           | invariant |
// | ---------------------------------- | ------------------- | --------------------------- | --------- |
// | `bool`                             | `bool`              | boxed value                 | `true` |
// | `i8`, `i16`, `i32`, `i64`, `isize` | same as Rust        | boxed value                 | width bounds |
// | `u8`, `u16`, `u32`, `u64`, `usize` | same as Rust        | boxed value                 | width bounds |
// | `&T`                               | `Ref<T>`            | constructor over values     | `inv<T>(deref(x))` |
// | `&mut T`                           | `Mut<T>`            | constructor over values     | `inv<T>(cur(x))` |
// | `(T0, .., Tn)`                     | `Tuple([T0, .., Tn])` | constructor over values   | conjunction of field invariants |
// | `struct S { f0: T0, .., fn: Tn }`  | `S`                 | constructor over values     | conjunction of field invariants |
//
// Notes:
// - `Mut<T>` additionally requires `cur(x) == fin(x)` when the mutable reference is closed.
// - Structs with `Drop`, generic structs, and recursive structs are unsupported.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::Once;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{
    AggregateKind, BasicBlock, BinOp, Body, BorrowKind, ConstOperand, Local, MutBorrowKind,
    Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::source_map::Spanned;
use rustc_span::{DUMMY_SP, Span};
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{FuncDecl, SatResult, Solver, SortKind};

use crate::prepass::{
    ContractParam, ControlPointDirective, ControlPointDirectives, DirectivePrepass,
    FunctionContract, LemmaCallContract, LoopContract, LoopContracts, ProgramPrepass,
    ResolvedExprEnv, SpecVarBinding, TypedGhostStmt, TypedLemmaDef, TypedPureFnDef,
    spec_ty_for_rust_ty,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{BinaryOp, SpecTy, TypedExpr, TypedExprKind, UnaryOp};
use crate::value_encoding::{
    InductiveEncoding, InductiveValue, PrimitiveValue, SymValue, TypeEncoding, TypeEncodingKind,
    ValueEncoder,
};

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
    model: BTreeMap<Local, SymValue>,
    ctrl: ControlPoint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BoolExpr {
    Const(bool),
    Value(SymValue),
    Not(Box<BoolExpr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AssertionKind {
    Universal,
    Existential,
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: Option<LocalDefId>,
    body: Option<Body<'tcx>>,
    contracts: HashMap<LocalDefId, FunctionContract>,
    function_spec_vars: HashMap<String, SymValue>,
    loop_contracts: LoopContracts,
    control_point_directives: ControlPointDirectives,
    pure_fns: HashMap<String, TypedPureFnDef>,
    lemmas: HashMap<String, TypedLemmaDef>,
    next_sym: Cell<usize>,
    value_encoder: ValueEncoder,
}

pub fn verify<'tcx>(tcx: TyCtxt<'tcx>, program: ProgramPrepass) -> Vec<VerificationResult> {
    let ProgramPrepass {
        ghosts,
        functions,
        contracts,
    } = program;
    let mut verifier = Verifier::new(tcx, contracts);
    for pure_fn in &ghosts.typed_pure_fns {
        if let Err(error) = verifier.load_ghost_function(pure_fn) {
            return vec![VerificationResult {
                function: "prepass".to_owned(),
                ..error
            }];
        }
    }
    for lemma in &ghosts.typed_lemmas {
        if let Err(error) = verifier.load_ghost_lemma(lemma) {
            return vec![VerificationResult {
                function: "prepass".to_owned(),
                ..error
            }];
        }
    }
    let mut results = Vec::new();
    for function in functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function.def_id)
            .steal();
        results.push(verifier.verify_function(function.def_id, body, function.prepass));
    }
    results
}

impl<'tcx> Verifier<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, contracts: HashMap<LocalDefId, FunctionContract>) -> Self {
        reset_solver();
        Self {
            tcx,
            def_id: None,
            body: None,
            contracts,
            function_spec_vars: HashMap::new(),
            loop_contracts: LoopContracts::empty(),
            control_point_directives: ControlPointDirectives::empty(),
            pure_fns: HashMap::new(),
            lemmas: HashMap::new(),
            next_sym: Cell::new(0),
            value_encoder: ValueEncoder::new(),
        }
    }

    fn current_def_id(&self) -> LocalDefId {
        self.def_id
            .expect("function verifier must load a function before use")
    }

    fn body(&self) -> &Body<'tcx> {
        self.body
            .as_ref()
            .expect("function verifier must load a body before use")
    }

    fn report_span(&self) -> Span {
        self.def_id
            .map(|def_id| self.tcx.def_span(def_id))
            .unwrap_or(DUMMY_SP)
    }

    fn report_function(&self) -> String {
        self.def_id
            .map(|def_id| self.tcx.def_path_str(def_id.to_def_id()))
            .unwrap_or_else(|| "prepass".to_owned())
    }

    pub fn load_ghost_function(
        &mut self,
        pure_fn: &TypedPureFnDef,
    ) -> Result<(), VerificationResult> {
        self.register_pure_fn(pure_fn)?;
        let inserted = self
            .pure_fns
            .insert(pure_fn.name.clone(), pure_fn.clone())
            .is_none();
        assert!(inserted, "duplicate pure function `{}`", pure_fn.name);
        Ok(())
    }

    pub fn load_ghost_lemma(&mut self, lemma: &TypedLemmaDef) -> Result<(), VerificationResult> {
        let inserted = self
            .lemmas
            .insert(lemma.name.clone(), lemma.clone())
            .is_none();
        assert!(inserted, "duplicate lemma `{}`", lemma.name);
        let mut stack = Vec::new();
        self.verify_lemma(lemma, &mut stack)
    }

    pub fn verify_function(
        &mut self,
        def_id: LocalDefId,
        body: Body<'tcx>,
        prepass: DirectivePrepass,
    ) -> VerificationResult {
        self.def_id = Some(def_id);
        self.body = Some(body);
        let DirectivePrepass {
            directives: _,
            loop_contracts,
            control_point_directives,
            function_contract,
            spec_vars,
        } = prepass;
        let contract = function_contract.expect("successful function prepass must yield contract");
        self.contracts.insert(self.current_def_id(), contract);
        self.loop_contracts = loop_contracts;
        self.control_point_directives = control_point_directives;
        self.function_spec_vars = self.instantiate_spec_vars(&spec_vars);

        let initial_state = match self.initial_state() {
            Ok(Some(state)) => state,
            Ok(None) => return self.pass_result("all assertions discharged"),
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
            if let Some(directives) = self
                .control_point_directives
                .directives_at(ctrl.basic_block, ctrl.statement_index)
            {
                let mut pruned = false;
                for directive in directives {
                    match directive {
                        ControlPointDirective::Assert(assertion) => {
                            let formula = match self.spec_expr_to_bool(
                                &state,
                                &assertion.assertion,
                                &assertion.resolution,
                            ) {
                                Ok(formula) => formula,
                                Err(err) => return err,
                            };
                            let formula = match self.bool_expr_to_z3(&formula) {
                                Ok(formula) => formula,
                                Err(err) => return err,
                            };
                            if let Err(err) = self.assert_expr_constraint(
                                &mut state,
                                &assertion.assertion,
                                formula,
                                self.control_span(ctrl),
                                assertion.assertion_span.clone(),
                                "assertion failed".to_owned(),
                            ) {
                                return err;
                            }
                        }
                        ControlPointDirective::Assume(assumption) => {
                            let formula = match self.spec_expr_to_bool(
                                &state,
                                &assumption.assumption,
                                &assumption.resolution,
                            ) {
                                Ok(formula) => formula,
                                Err(err) => return err,
                            };
                            let formula = match self.bool_expr_to_z3(&formula) {
                                Ok(formula) => formula,
                                Err(err) => return err,
                            };
                            match self.assume_constraint(
                                &mut state,
                                formula,
                                self.control_span(ctrl),
                            ) {
                                Ok(true) => {}
                                Ok(false) => {
                                    pruned = true;
                                    break;
                                }
                                Err(err) => return err,
                            }
                        }
                        ControlPointDirective::LemmaCall(lemma_call) => {
                            match self.execute_lemma_call(
                                &mut state,
                                lemma_call,
                                self.control_span(ctrl),
                            ) {
                                Ok(true) => {}
                                Ok(false) => {
                                    pruned = true;
                                    break;
                                }
                                Err(err) => return err,
                            }
                        }
                    }
                }
                if pruned {
                    continue;
                }
            }
            let data = &self.body().basic_blocks[ctrl.basic_block];
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

    fn initial_state(&self) -> Result<Option<State>, VerificationResult> {
        let mut state = State {
            pc: Bool::from_bool(true),
            model: BTreeMap::new(),
            ctrl: ControlPoint {
                basic_block: BasicBlock::from_usize(0),
                statement_index: 0,
            },
        };
        for local in self
            .body()
            .local_decls
            .indices()
            .take(self.body().arg_count + 1)
        {
            let ty = self.body().local_decls[local].ty;
            let value = self.fresh_for_rust_ty(ty, &format!("arg_{}", local.as_usize()))?;
            state.model.insert(local, value);
        }
        if let Some(contract) = self.contracts.get(&self.current_def_id()) {
            let env =
                CallEnv::for_function(self, &state, contract, self.function_spec_vars.clone())?;
            let req = self.contract_req_to_z3(contract, &env, self.report_span())?;
            if !self.assume_constraint(&mut state, req, self.report_span())? {
                return Ok(None);
            }
        }
        Ok(Some(state))
    }

    fn step_statement(
        &self,
        mut state: State,
        stmt: &Statement<'tcx>,
    ) -> Result<State, VerificationResult> {
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                let ty = self.body().local_decls[*local].ty;
                let value = self.fresh_for_rust_ty(ty, &format!("live_{}", local.as_usize()))?;
                state.model.insert(*local, value);
            }
            StatementKind::StorageDead(local) => {
                let ty = self.body().local_decls[*local].ty;
                if self.ty_contains_mut_ref(ty) {
                    self.resolve_and_remove_local(&mut state, *local, stmt.source_info.span)?;
                }
            }
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                let value = self.eval_rvalue(&mut state, rvalue, stmt.source_info.span)?;
                self.write_place(&mut state, *place, value, stmt.source_info.span)?;
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
                if let Some(contract) = self.contracts.get(&self.current_def_id()) {
                    let formula = self.function_postcondition_to_z3(&state, contract)?;
                    self.assert_expr_constraint(
                        &mut state,
                        &contract.ens,
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
                    let branch = match discr.ty(self.body(), self.tcx).kind() {
                        TyKind::Bool => {
                            if value == 0 {
                                not_expr(BoolExpr::Value(discr_value.clone()))
                            } else {
                                BoolExpr::Value(discr_value.clone())
                            }
                        }
                        _ => BoolExpr::Value(self.value_wrap_bool(&self.eq_for_spec_ty(
                            &self.spec_ty_for_place_ty(
                                discr.ty(&self.body().local_decls, self.tcx),
                                term.source_info.span,
                            )?,
                            &discr_value,
                            &self.value_int(value as i64),
                            term.source_info.span,
                        )?)),
                    };
                    let branch = self.bool_expr_to_z3(&branch)?;
                    seen_conditions.push(branch.clone());
                    if let Some(next) =
                        self.prune_state(state.clone(), branch, term.source_info.span)?
                        && let Some(loop_state) =
                            self.transition_to_block(next, target, term.source_info.span)?
                    {
                        next_states.push(loop_state);
                    }
                }
                if let Some(otherwise) = self.prune_state(
                    state,
                    bool_not(bool_or(seen_conditions)),
                    term.source_info.span,
                )? && let Some(loop_state) =
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
                let mut formula = BoolExpr::Value(cond_value);
                if !*expected {
                    formula = not_expr(formula);
                }
                let formula = self.bool_expr_to_z3(&formula)?;
                self.assert_constraint(
                    &mut state,
                    formula,
                    AssertionKind::Universal,
                    term.source_info.span,
                    span_text(self.tcx, term.source_info.span),
                    format!("assertion failed: {msg:?}"),
                )?;
                self.goto_target(state, *target, term.source_info.span)
            }
            TerminatorKind::Drop { place, target, .. } => {
                if place.projection.is_empty() {
                    if self.is_immediate_return_block(*target) {
                        self.resolve_local(&mut state, place.local, term.source_info.span)?;
                    } else {
                        self.resolve_and_remove_local(
                            &mut state,
                            place.local,
                            term.source_info.span,
                        )?;
                    }
                    self.goto_target(state, *target, term.source_info.span)
                } else {
                    Err(self.unsupported_result(
                        term.source_info.span,
                        format!("unsupported MIR terminator {:?}", term.kind),
                    ))
                }
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
        if let Some(def_id) = callee {
            let contract = self
                .contracts
                .get(&def_id)
                .ok_or_else(|| self.missing_local_contract_result(def_id, span))?;
            let spec = self.instantiate_contract_spec_vars(contract);
            let env = self.call_env(&state, args, contract, span, spec.clone())?;
            let req = self.contract_req_to_z3(contract, &env, span)?;
            self.assert_expr_constraint(
                &mut state,
                &contract.req,
                req,
                span,
                contract.req_span.clone(),
                "precondition failed".to_owned(),
            )?;
            let result_ty = self.place_ty(destination);
            let result_value = self.fresh_for_rust_ty(result_ty, "call_result")?;
            self.write_place(&mut state, destination, result_value.clone(), span)?;
            self.abstract_call_mut_args(&mut state, args, span)?;
            let mut env = self.call_env(&state, args, contract, span, spec)?;
            self.consume_call_move_args(&mut state, args, span)?;
            env.current.insert("result".to_owned(), result_value);
            let ens = self.contract_ens_to_z3(contract, &env, span)?;
            if !self.assume_constraint(&mut state, ens, span)? {
                return Ok(Vec::new());
            }
        } else {
            let result_ty = self.place_ty(destination);
            let result_value = self.fresh_for_rust_ty(result_ty, "opaque_result")?;
            self.require_type_invariant(
                &mut state,
                result_ty,
                &result_value,
                span,
                "type invariant does not hold".to_owned(),
            )?;
            self.write_place(&mut state, destination, result_value, span)?;
            self.abstract_call_mut_args(&mut state, args, span)?;
            self.consume_call_move_args(&mut state, args, span)?;
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
            let invariant = self.spec_expr_to_bool(
                &state,
                &loop_contract.invariant,
                &loop_contract.resolution,
            )?;
            let invariant = self.bool_expr_to_z3(&invariant)?;
            self.assert_expr_constraint(
                &mut state,
                &loop_contract.invariant,
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
                if !self.assume_constraint(&mut abstract_state, invariant, span)? {
                    return Ok(None);
                }
                abstract_state.pc = bool_and(vec![abstract_state.pc, self.loop_marker(target)]);
                abstract_state.ctrl = ControlPoint {
                    basic_block: target,
                    statement_index: 0,
                };
                return Ok(Some(abstract_state));
            }
        }

        if let Some(header) = self.loop_contracts.header_for_invariant_block(target)
            && let Some(loop_contract) = self.loop_contracts.contract_by_header(header)
        {
            let invariant = self.spec_expr_to_bool(
                &state,
                &loop_contract.invariant,
                &loop_contract.resolution,
            )?;
            let invariant = self.bool_expr_to_z3(&invariant)?;
            if !self.assume_constraint(&mut state, invariant, span)? {
                return Ok(None);
            }
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
            model: BTreeMap::new(),
            ctrl,
        };
        let pcs = states
            .iter()
            .map(|state| state.pc.clone())
            .collect::<Vec<_>>();
        merged.pc = Bool::or(&pcs);

        for local in shared {
            let ty = self.body().local_decls[local].ty;
            let spec_ty = self.spec_ty_for_place_ty(ty, self.control_span(ctrl))?;
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
                let equality = self.eq_for_spec_ty(
                    &spec_ty,
                    &merged_value,
                    &incoming,
                    self.control_span(state.ctrl),
                )?;
                self.add_path_condition(&mut merged, state.pc.clone().implies(equality));
            }
            merged.model.insert(local, merged_value);
        }

        match self.check_sat(std::slice::from_ref(&merged.pc)) {
            SatResult::Sat => Ok(Some(merged)),
            SatResult::Unsat => Ok(None),
            SatResult::Unknown => Err(self.unknown_result(
                self.control_span(ctrl),
                "solver returned unknown while checking merged path feasibility".to_owned(),
            )),
        }
    }

    fn enqueue_state(
        &self,
        pending: &mut BTreeMap<ControlPoint, Vec<State>>,
        worklist: &mut VecDeque<ControlPoint>,
        state: State,
    ) -> Option<VerificationResult> {
        let ctrl = state.ctrl;
        let bucket = pending.entry(ctrl).or_default();
        if bucket.is_empty() {
            worklist.push_back(ctrl);
        }
        bucket.push(state);
        None
    }

    fn register_pure_fn(&self, pure_fn: &TypedPureFnDef) -> Result<(), VerificationResult> {
        let decl = self.pure_fn_decl(pure_fn)?;
        let mut current = HashMap::new();
        let mut vars = Vec::with_capacity(pure_fn.params.len());
        for param in &pure_fn.params {
            let value = self
                .fresh_for_spec_ty(&param.ty, &format!("pure_{}_{}", pure_fn.name, param.name))?;
            current.insert(param.name.clone(), value.clone());
            vars.push(value);
        }
        let spec = HashMap::new();
        let body = self.contract_expr_to_value(&current, &spec, &pure_fn.body)?;
        let fn_value =
            self.apply_pure_fn_decl(&decl, &pure_fn.result_ty, &vars, self.report_span())?;
        let mut consequent =
            vec![self.eq_for_spec_ty(&pure_fn.result_ty, &fn_value, &body, self.report_span())?];
        if let Some(formula) =
            self.spec_ty_formula(&pure_fn.result_ty, &fn_value, self.report_span())?
        {
            consequent.push(formula);
        }
        let mut antecedent = Vec::new();
        for (param, value) in pure_fn.params.iter().zip(vars.iter()) {
            if let Some(formula) = self.spec_ty_formula(&param.ty, value, self.report_span())? {
                antecedent.push(formula);
            }
        }
        let body = if antecedent.is_empty() {
            bool_and(consequent)
        } else {
            bool_and(antecedent).implies(bool_and(consequent))
        };
        let asts: Vec<&dyn Ast> = vars.iter().map(sym_value_ast).collect();
        with_solver(|solver| {
            solver.assert(z3::ast::forall_const(&asts, &[], &body));
        });
        Ok(())
    }

    fn verify_lemma(
        &self,
        lemma: &TypedLemmaDef,
        stack: &mut Vec<String>,
    ) -> Result<(), VerificationResult> {
        if stack.iter().any(|name| name == &lemma.name) {
            return Err(self.unsupported_result(
                self.report_span(),
                format!("recursive lemma `{}` is not supported", lemma.name),
            ));
        }
        stack.push(lemma.name.clone());
        let mut current = HashMap::new();
        for param in &lemma.params {
            let value =
                self.fresh_for_spec_ty(&param.ty, &format!("lemma_{}_{}", lemma.name, param.name))?;
            current.insert(param.name.clone(), value);
        }
        let spec = self.instantiate_spec_vars(&lemma.spec_vars);
        let mut state = State {
            pc: Bool::from_bool(true),
            model: BTreeMap::new(),
            ctrl: ControlPoint {
                basic_block: BasicBlock::from_usize(0),
                statement_index: 0,
            },
        };
        let req = self.contract_expr_to_bool(&current, &spec, &lemma.req)?;
        if !self.assume_constraint(&mut state, self.bool_expr_to_z3(&req)?, self.report_span())? {
            stack.pop();
            return Ok(());
        }
        for param in &lemma.params {
            let value = current.get(&param.name).expect("lemma parameter value");
            if let Some(formula) = self.spec_ty_formula(&param.ty, value, self.report_span())?
                && !self.assume_constraint(&mut state, formula, self.report_span())?
            {
                stack.pop();
                return Ok(());
            }
        }
        for stmt in &lemma.body {
            match stmt {
                TypedGhostStmt::Assert(expr) => {
                    let formula = self.contract_expr_to_bool(&current, &spec, expr)?;
                    self.assert_expr_constraint(
                        &mut state,
                        expr,
                        self.bool_expr_to_z3(&formula)?,
                        self.report_span(),
                        format!("lemma `{}`", lemma.name),
                        format!("lemma `{}` assertion failed", lemma.name),
                    )?;
                }
                TypedGhostStmt::Assume(expr) => {
                    let formula = self.contract_expr_to_bool(&current, &spec, expr)?;
                    if !self.assume_constraint(
                        &mut state,
                        self.bool_expr_to_z3(&formula)?,
                        self.report_span(),
                    )? {
                        stack.pop();
                        return Ok(());
                    }
                }
                TypedGhostStmt::Call { lemma_name, args } => {
                    let callee = self.lemmas.get(lemma_name).ok_or_else(|| {
                        self.unsupported_result(
                            self.report_span(),
                            format!("unknown lemma `{lemma_name}`"),
                        )
                    })?;
                    self.verify_lemma(callee, stack)?;
                    let env = self.lemma_env_from_contract_args(args, &current, &spec, callee)?;
                    let req = self.contract_expr_to_bool(&env.current, &env.spec, &callee.req)?;
                    self.assert_expr_constraint(
                        &mut state,
                        &callee.req,
                        self.bool_expr_to_z3(&req)?,
                        self.report_span(),
                        format!("lemma `{}`", lemma.name),
                        format!("lemma `{}` precondition failed", callee.name),
                    )?;
                    let ens = self.contract_expr_to_bool(&env.current, &env.spec, &callee.ens)?;
                    if !self.assume_constraint(
                        &mut state,
                        self.bool_expr_to_z3(&ens)?,
                        self.report_span(),
                    )? {
                        stack.pop();
                        return Ok(());
                    }
                }
            }
        }
        let ens = self.contract_expr_to_bool(&current, &spec, &lemma.ens)?;
        let result = self.assert_expr_constraint(
            &mut state,
            &lemma.ens,
            self.bool_expr_to_z3(&ens)?,
            self.report_span(),
            format!("lemma `{}`", lemma.name),
            format!("lemma `{}` postcondition failed", lemma.name),
        );
        stack.pop();
        result
    }

    fn execute_lemma_call(
        &self,
        state: &mut State,
        call: &LemmaCallContract,
        span: Span,
    ) -> Result<bool, VerificationResult> {
        let lemma = self.lemmas.get(&call.lemma_name).ok_or_else(|| {
            self.unsupported_result(span, format!("unknown lemma `{}`", call.lemma_name))
        })?;
        let env = self.lemma_env_from_state_exprs(state, &call.args, &call.resolution, lemma)?;
        let req = self.contract_expr_to_bool(&env.current, &env.spec, &lemma.req)?;
        self.assert_expr_constraint(
            state,
            &lemma.req,
            self.bool_expr_to_z3(&req)?,
            span,
            call.span_text.clone(),
            format!("lemma `{}` precondition failed", lemma.name),
        )?;
        let ens = self.contract_expr_to_bool(&env.current, &env.spec, &lemma.ens)?;
        self.assume_constraint(state, self.bool_expr_to_z3(&ens)?, span)
    }

    fn lemma_env_from_state_exprs(
        &self,
        state: &State,
        args: &[TypedExpr],
        resolution: &ResolvedExprEnv,
        lemma: &TypedLemmaDef,
    ) -> Result<CallEnv, VerificationResult> {
        if lemma.params.len() != args.len() {
            return Err(self.unsupported_result(
                self.control_span(state.ctrl),
                format!(
                    "lemma `{}` parameter count mismatch: expected {}, found {}",
                    lemma.name,
                    lemma.params.len(),
                    args.len()
                ),
            ));
        }
        let mut current = HashMap::new();
        for (param, arg) in lemma.params.iter().zip(args.iter()) {
            let value = self.spec_expr_to_value(state, arg, resolution)?;
            current.insert(param.name.clone(), value);
        }
        Ok(CallEnv {
            current,
            spec: self.instantiate_spec_vars(&lemma.spec_vars),
        })
    }

    fn lemma_env_from_contract_args(
        &self,
        args: &[TypedExpr],
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
        lemma: &TypedLemmaDef,
    ) -> Result<CallEnv, VerificationResult> {
        if lemma.params.len() != args.len() {
            return Err(self.unsupported_result(
                self.report_span(),
                format!(
                    "lemma `{}` parameter count mismatch: expected {}, found {}",
                    lemma.name,
                    lemma.params.len(),
                    args.len()
                ),
            ));
        }
        let mut call_current = HashMap::new();
        for (param, arg) in lemma.params.iter().zip(args.iter()) {
            let value = self.contract_expr_to_value(current, spec, arg)?;
            call_current.insert(param.name.clone(), value);
        }
        Ok(CallEnv {
            current: call_current,
            spec: self.instantiate_spec_vars(&lemma.spec_vars),
        })
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
        self.require_resolve_formula(state, local, &value, span)
    }

    fn resolve_local(
        &self,
        state: &mut State,
        local: Local,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let Some(value) = state.model.get(&local).cloned() else {
            return Ok(());
        };
        self.require_resolve_formula(state, local, &value, span)
    }

    fn require_resolve_formula(
        &self,
        state: &mut State,
        local: Local,
        value: &SymValue,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let ty = self.body().local_decls[local].ty;
        let formula = self.resolve_formula(ty, value, span)?;
        self.assert_constraint(
            state,
            formula,
            AssertionKind::Universal,
            span,
            span_text(self.tcx, span),
            "mutable reference close failed".to_owned(),
        )?;
        Ok(())
    }

    fn resolve_formula(
        &self,
        ty: Ty<'tcx>,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let spec_ty =
            spec_ty_for_rust_ty(self.tcx, ty).map_err(|err| self.unsupported_result(span, err))?;
        self.resolve_formula_for_spec_ty(&spec_ty, value, span)
    }

    fn eval_rvalue(
        &self,
        state: &mut State,
        rvalue: &Rvalue<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match rvalue {
            Rvalue::Use(operand) => self.eval_operand(state, operand, span),
            Rvalue::Ref(_, borrow_kind, place) => match borrow_kind {
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default | MutBorrowKind::TwoPhaseBorrow,
                } => self.create_mut_borrow(state, *place, span),
                BorrowKind::Shared => self.create_shared_borrow(state, *place, span),
                _ => Err(self
                    .unsupported_result(span, format!("unsupported borrow kind {borrow_kind:?}"))),
            },
            Rvalue::BinaryOp(op, operands) => {
                self.eval_binary_op(state, *op, &operands.0, &operands.1, span)
            }
            Rvalue::UnaryOp(op, operand) => self.eval_unary_op(state, *op, operand, span),
            Rvalue::Aggregate(kind, operands) => match **kind {
                AggregateKind::Tuple => {
                    let result_ty = self.spec_ty_for_place_ty(
                        rvalue.ty(&self.body().local_decls, self.tcx),
                        span,
                    )?;
                    let mut values = Vec::with_capacity(operands.len());
                    for operand in operands {
                        values.push(self.eval_operand(state, operand, span)?);
                    }
                    self.construct_datatype(&result_ty, &values)
                }
                AggregateKind::Adt(def_id, variant_idx, args, _, _) => {
                    let adt_def = self.tcx.adt_def(def_id);
                    if !adt_def.is_struct() || variant_idx.as_usize() != 0 {
                        return Err(self
                            .unsupported_result(span, format!("unsupported aggregate {kind:?}")));
                    }
                    let field_tys = self.adt_field_tys(adt_def, args);
                    let mut values = Vec::with_capacity(field_tys.len());
                    for operand in operands {
                        values.push(self.eval_operand(state, operand, span)?);
                    }
                    let result_ty = spec_ty_for_rust_ty(
                        self.tcx,
                        rvalue.ty(&self.body().local_decls, self.tcx),
                    )
                    .map_err(|err| self.unsupported_result(span, err))?;
                    self.construct_datatype(&result_ty, &values)
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
    ) -> Result<SymValue, VerificationResult> {
        let current = self.read_place(state, place, ReadMode::Current, span)?;
        let final_value = if self.is_reborrow(place) {
            self.read_place(state, place, ReadMode::Final, span)?
        } else {
            let ty = self.place_ty(place);
            self.fresh_for_rust_ty(ty, "prophecy")?
        };
        self.write_place(state, place, final_value.clone(), span)?;
        let inner_ty = self.spec_ty_for_place_ty(self.place_ty(place), span)?;
        self.construct_datatype(&SpecTy::Mut(Box::new(inner_ty)), &[current, final_value])
    }

    fn create_shared_borrow(
        &self,
        state: &State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = self.read_place(state, place, ReadMode::Current, span)?;
        let inner_ty = self.spec_ty_for_place_ty(self.place_ty(place), span)?;
        self.construct_datatype(&SpecTy::Ref(Box::new(inner_ty)), &[value])
    }

    fn eval_binary_op(
        &self,
        state: &mut State,
        op: BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let lhs_value = self.eval_operand(state, lhs, span)?;
        let rhs_value = self.eval_operand(state, rhs, span)?;
        let lhs_ty = lhs.ty(&self.body().local_decls, self.tcx);
        let lhs_spec_ty = self.spec_ty_for_place_ty(lhs_ty, span)?;
        let result = match op {
            BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow => {
                self.eval_checked_binary_op(state, op, lhs, rhs, span)
            }
            BinOp::Add => {
                let int_value = self.value_int_data(&lhs_value) + self.value_int_data(&rhs_value);
                self.require_int_invariant(
                    state,
                    lhs_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_wrap_int(&int_value))
            }
            BinOp::Sub => {
                let int_value = self.value_int_data(&lhs_value) - self.value_int_data(&rhs_value);
                self.require_int_invariant(
                    state,
                    lhs_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_wrap_int(&int_value))
            }
            BinOp::Mul => {
                let int_value = self.value_int_data(&lhs_value) * self.value_int_data(&rhs_value);
                self.require_int_invariant(
                    state,
                    lhs_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_wrap_int(&int_value))
            }
            BinOp::Eq => Ok(self.value_wrap_bool(&self.eq_for_spec_ty(
                &lhs_spec_ty,
                &lhs_value,
                &rhs_value,
                span,
            )?)),
            BinOp::Ne => Ok(self.value_wrap_bool(
                &self
                    .eq_for_spec_ty(&lhs_spec_ty, &lhs_value, &rhs_value, span)?
                    .not(),
            )),
            BinOp::Lt => Ok(self.value_wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .lt(self.value_int_data(&rhs_value)),
            )),
            BinOp::Le => Ok(self.value_wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .le(self.value_int_data(&rhs_value)),
            )),
            BinOp::Gt => Ok(self.value_wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .gt(self.value_int_data(&rhs_value)),
            )),
            BinOp::Ge => Ok(self.value_wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .ge(self.value_int_data(&rhs_value)),
            )),
            other => {
                Err(self.unsupported_result(span, format!("unsupported binary operator {other:?}")))
            }
        }?;
        Ok(result)
    }

    fn eval_checked_binary_op(
        &self,
        state: &mut State,
        op: BinOp,
        lhs: &Operand<'tcx>,
        rhs: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let lhs_value = self.eval_operand(state, lhs, span)?;
        let rhs_value = self.eval_operand(state, rhs, span)?;
        let result_ty = lhs.ty(&self.body().local_decls, self.tcx);
        let tuple_ty = SpecTy::Tuple(vec![
            self.spec_ty_for_place_ty(result_ty, span)?,
            SpecTy::Bool,
        ]);
        let result_value = match op {
            BinOp::Add | BinOp::AddWithOverflow => {
                let int_value = self.value_int_data(&lhs_value) + self.value_int_data(&rhs_value);
                self.require_int_invariant(
                    state,
                    result_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                self.value_wrap_int(&int_value)
            }
            BinOp::Sub | BinOp::SubWithOverflow => {
                let int_value = self.value_int_data(&lhs_value) - self.value_int_data(&rhs_value);
                self.require_int_invariant(
                    state,
                    result_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                self.value_wrap_int(&int_value)
            }
            BinOp::Mul | BinOp::MulWithOverflow => {
                let int_value = self.value_int_data(&lhs_value) * self.value_int_data(&rhs_value);
                self.require_int_invariant(
                    state,
                    result_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                self.value_wrap_int(&int_value)
            }
            other => {
                return Err(self.unsupported_result(
                    span,
                    format!("unsupported checked binary operator {other:?}"),
                ));
            }
        };
        let overflow_value = self.overflow_value_for_result(result_ty, &result_value, span)?;
        self.construct_datatype(&tuple_ty, &[result_value, overflow_value])
    }

    fn eval_unary_op(
        &self,
        state: &mut State,
        op: UnOp,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = self.eval_operand(state, operand, span)?;
        let operand_ty = operand.ty(&self.body().local_decls, self.tcx);
        let result = match op {
            UnOp::Not => match operand_ty.kind() {
                TyKind::Bool => Ok(self.value_wrap_bool(&self.value_bool_data(&value).not())),
                _ => Ok(self.value_wrap_bool(&self.value_bool_data(&value).not())),
            },
            UnOp::Neg => {
                let int_value = Int::from_i64(0) - self.value_int_data(&value);
                self.require_int_invariant(
                    state,
                    operand_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_wrap_int(&int_value))
            }
            other => {
                Err(self.unsupported_result(span, format!("unsupported unary operator {other:?}")))
            }
        }?;
        Ok(result)
    }

    fn eval_operand(
        &self,
        state: &mut State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = self.read_operand(state, operand, span)?;
        if let Operand::Constant(constant) = operand {
            self.require_type_invariant(
                state,
                constant.const_.ty(),
                &value,
                span,
                "type invariant does not hold".to_owned(),
            )?;
        }
        if matches!(operand, Operand::Move(_)) {
            self.consume_operand(state, operand, span)?;
        }
        Ok(value)
    }

    fn read_operand(
        &self,
        state: &State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.read_place(state, *place, ReadMode::Current, span)
            }
            Operand::Constant(constant) => self.eval_const_operand(constant, span),
        }
    }

    fn consume_operand(
        &self,
        state: &mut State,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        match operand {
            Operand::Copy(_) => Ok(()),
            Operand::Move(place) => {
                if place.projection.is_empty() {
                    state.model.remove(&place.local);
                } else {
                    self.dangle_place(state, *place, span)?;
                }
                Ok(())
            }
            Operand::Constant(_) => Ok(()),
        }
    }

    fn eval_const_operand(
        &self,
        constant: &ConstOperand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
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
                Ok(self.value_bool(value.try_to_bool().map_err(|_| {
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
                self.scalar_int_to_value(ty, value, span)
            }
            TyKind::Tuple(fields) if fields.is_empty() => {
                let spec_ty = self.spec_ty_for_place_ty(ty, span)?;
                self.construct_datatype(&spec_ty, &[])
            }
            TyKind::Adt(adt_def, _)
                if adt_def.is_struct() && adt_def.non_enum_variant().fields.is_empty() =>
            {
                let spec_ty = self.spec_ty_for_place_ty(ty, span)?;
                self.construct_datatype(&spec_ty, &[])
            }
            _ => Err(self.unsupported_result(span, format!("unsupported constant type {ty:?}"))),
        }
    }

    fn read_place(
        &self,
        state: &State,
        place: Place<'tcx>,
        mode: ReadMode,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let Some(root) = state.model.get(&place.local).cloned() else {
            return Err(
                self.unsupported_result(span, format!("missing local {}", place.local.as_usize()))
            );
        };
        let root_ty = self.body().local_decls[place.local].ty;
        let root_spec_ty = self.spec_ty_for_place_ty(root_ty, span)?;
        self.read_projection(root, &root_spec_ty, place.as_ref().projection, mode, span)
    }

    fn read_projection(
        &self,
        value: SymValue,
        spec_ty: &SpecTy,
        projection: &[PlaceElem<'tcx>],
        mode: ReadMode,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        if projection.is_empty() {
            return Ok(value);
        }
        match projection[0] {
            PlaceElem::Deref => {
                let next = if matches!(spec_ty, SpecTy::Mut(_)) {
                    let inner_ty = self.deref_spec_ty(spec_ty).expect("typed deref");
                    match mode {
                        ReadMode::Current => self.mut_cur(&value, inner_ty, span)?,
                        ReadMode::Final => self.mut_fin(&value, inner_ty, span)?,
                    }
                } else if matches!(spec_ty, SpecTy::Ref(_)) {
                    let inner_ty = self.deref_spec_ty(spec_ty).expect("typed deref");
                    self.ref_deref(&value, inner_ty, span)?
                } else {
                    return Err(
                        self.unsupported_result(span, "deref of non-reference place".to_owned())
                    );
                };
                let Some(inner_spec_ty) = self.deref_spec_ty(spec_ty) else {
                    return Err(
                        self.unsupported_result(span, "deref of non-reference place".to_owned())
                    );
                };
                self.read_projection(next, inner_spec_ty, &projection[1..], mode, span)
            }
            PlaceElem::Field(field, _) => {
                let next = self.project_field(value, spec_ty, field.index(), span)?;
                let Some(field_spec_ty) = self.composite_spec_field_ty(spec_ty, field.index())
                else {
                    return Err(self.unsupported_result(
                        span,
                        "field projection on non-composite place".to_owned(),
                    ));
                };
                self.read_projection(next, field_spec_ty, &projection[1..], mode, span)
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
        value: SymValue,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let root = state
            .model
            .get(&place.local)
            .cloned()
            .unwrap_or_else(|| value.clone());
        let root_ty = self.body().local_decls[place.local].ty;
        let root_spec_ty = self.spec_ty_for_place_ty(root_ty, span)?;
        let updated =
            self.write_projection(root, &root_spec_ty, place.as_ref().projection, value, span)?;
        state.model.insert(place.local, updated);
        Ok(())
    }

    fn write_projection(
        &self,
        value: SymValue,
        spec_ty: &SpecTy,
        projection: &[PlaceElem<'tcx>],
        replacement: SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        if projection.is_empty() {
            return Ok(replacement);
        }
        match projection[0] {
            PlaceElem::Deref => {
                if matches!(spec_ty, SpecTy::Ref(_)) {
                    return Err(self.unsupported_result(
                        span,
                        "assignment through shared reference is unsupported".to_owned(),
                    ));
                }
                let Some(inner_spec_ty) = self.deref_spec_ty(spec_ty) else {
                    return Err(self.unsupported_result(
                        span,
                        "deref assignment on non-reference place".to_owned(),
                    ));
                };
                let SpecTy::Mut(inner_ty) = spec_ty else {
                    unreachable!("shared refs rejected above");
                };
                let current = self.write_projection(
                    self.mut_cur(&value, inner_ty, span)?,
                    inner_spec_ty,
                    &projection[1..],
                    replacement,
                    span,
                )?;
                let fin = self.mut_fin(&value, inner_ty, span)?;
                self.construct_datatype(spec_ty, &[current, fin])
            }
            PlaceElem::Field(field, _) => {
                let index = field.index();
                let field_count = self.composite_spec_field_count(spec_ty).ok_or_else(|| {
                    self.unsupported_result(
                        span,
                        "field assignment on non-composite place".to_owned(),
                    )
                })?;
                let Some(field_spec_ty) = self.composite_spec_field_ty(spec_ty, index) else {
                    return Err(
                        self.unsupported_result(span, "field index out of range".to_owned())
                    );
                };
                let mut items = Vec::with_capacity(field_count);
                for current_index in 0..field_count {
                    let field_value =
                        self.project_field(value.clone(), spec_ty, current_index, span)?;
                    if current_index == index {
                        items.push(self.write_projection(
                            field_value,
                            field_spec_ty,
                            &projection[1..],
                            replacement.clone(),
                            span,
                        )?);
                    } else {
                        items.push(field_value);
                    }
                }
                self.construct_datatype(spec_ty, &items)
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
        let place_spec_ty = self.spec_ty_for_place_ty(self.place_ty(place), span)?;
        let updated = self.dangle_value(&place_spec_ty, &value, span)?;
        self.write_place(state, place, updated, span)
    }

    fn dangle_value(
        &self,
        spec_ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match spec_ty {
            SpecTy::Tuple(items) => {
                let mut updated = Vec::with_capacity(items.len());
                for (index, field_ty) in items.iter().enumerate() {
                    let field_value = self.project_field(value.clone(), spec_ty, index, span)?;
                    updated.push(self.dangle_value(field_ty, &field_value, span)?);
                }
                self.construct_datatype(spec_ty, &updated)
            }
            SpecTy::Struct(struct_ty) => {
                let mut updated = Vec::with_capacity(struct_ty.fields.len());
                for (index, field_ty) in struct_ty.fields.iter().enumerate() {
                    let field_value = self.project_field(value.clone(), spec_ty, index, span)?;
                    updated.push(self.dangle_value(&field_ty.ty, &field_value, span)?);
                }
                self.construct_datatype(spec_ty, &updated)
            }
            SpecTy::Mut(inner) => {
                let fresh = self.fresh_for_spec_ty(inner, "dangle")?;
                let fin = self.mut_fin(value, inner, span)?;
                self.construct_datatype(spec_ty, &[fresh, fin])
            }
            SpecTy::Ref(_)
            | SpecTy::Bool
            | SpecTy::IntLiteral
            | SpecTy::I8
            | SpecTy::I16
            | SpecTy::I32
            | SpecTy::I64
            | SpecTy::Isize
            | SpecTy::U8
            | SpecTy::U16
            | SpecTy::U32
            | SpecTy::U64
            | SpecTy::Usize => Ok(value.clone()),
        }
    }

    fn spec_expr_to_bool(
        &self,
        state: &State,
        expr: &TypedExpr,
        resolved: &ResolvedExprEnv,
    ) -> Result<BoolExpr, VerificationResult> {
        match &expr.kind {
            TypedExprKind::Bool(value) => Ok(BoolExpr::Const(*value)),
            _ => Ok(BoolExpr::Value(
                self.spec_expr_to_value(state, expr, resolved)?,
            )),
        }
    }

    fn spec_expr_to_value(
        &self,
        state: &State,
        expr: &TypedExpr,
        resolved: &ResolvedExprEnv,
    ) -> Result<SymValue, VerificationResult> {
        match &expr.kind {
            TypedExprKind::Bool(value) => Ok(self.value_bool(*value)),
            TypedExprKind::Int(value) => {
                self.value_decimal_int(&value.digits, self.control_span(state.ctrl))
            }
            TypedExprKind::Var(name) if resolved.spec_vars.contains(name) => {
                self.function_spec_vars.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            TypedExprKind::Var(name) => {
                let Some(local) = resolved.locals.get(name) else {
                    return Err(self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing local binding `{name}`"),
                    ));
                };
                state.model.get(local).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing local {}", local.as_usize()),
                    )
                })
            }
            TypedExprKind::Bind(name) => {
                self.function_spec_vars.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            TypedExprKind::PureCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.spec_expr_to_value(state, arg, resolved)?);
                }
                self.eval_pure_call(func, &expr.ty, values, self.control_span(state.ctrl))
            }
            TypedExprKind::Field { base, index, .. } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                self.project_field(value, &base.ty, *index, self.control_span(state.ctrl))
            }
            TypedExprKind::TupleField { base, index } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                self.project_field(value, &base.ty, *index, self.control_span(state.ctrl))
            }
            TypedExprKind::Deref { base } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                match &base.ty {
                    crate::spec::SpecTy::Ref(inner) => {
                        self.ref_deref(&value, inner, self.control_span(state.ctrl))
                    }
                    crate::spec::SpecTy::Mut(inner) => {
                        self.mut_cur(&value, inner, self.control_span(state.ctrl))
                    }
                    _ => unreachable!("typed deref base"),
                }
            }
            TypedExprKind::Fin { base } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                let SpecTy::Mut(inner) = &base.ty else {
                    unreachable!("typed fin base");
                };
                self.mut_fin(&value, inner, self.control_span(state.ctrl))
            }
            TypedExprKind::Unary { op, arg } => {
                let value = self.spec_expr_to_value(state, arg, resolved)?;
                Ok(self.lower_unary_value(*op, &value))
            }
            TypedExprKind::Binary { op, lhs, rhs } => {
                let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                self.lower_binary_value(
                    *op,
                    &lhs.ty,
                    &lhs_value,
                    &rhs_value,
                    self.control_span(state.ctrl),
                )
            }
        }
    }

    fn contract_expr_to_bool(
        &self,
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
        expr: &TypedExpr,
    ) -> Result<BoolExpr, VerificationResult> {
        match &expr.kind {
            TypedExprKind::Bool(value) => Ok(BoolExpr::Const(*value)),
            _ => Ok(BoolExpr::Value(
                self.contract_expr_to_value(current, spec, expr)?,
            )),
        }
    }

    fn contract_expr_to_value(
        &self,
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
        expr: &TypedExpr,
    ) -> Result<SymValue, VerificationResult> {
        match &expr.kind {
            TypedExprKind::Bool(value) => Ok(self.value_bool(*value)),
            TypedExprKind::Int(value) => self.value_decimal_int(&value.digits, self.report_span()),
            TypedExprKind::Var(name) if spec.contains_key(name) => {
                spec.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.report_span(),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            TypedExprKind::Var(name) => current.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.report_span(),
                    format!("missing contract binding `{name}`"),
                )
            }),
            TypedExprKind::Bind(name) => spec.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.report_span(),
                    format!("missing spec binding `{name}`"),
                )
            }),
            TypedExprKind::PureCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.contract_expr_to_value(current, spec, arg)?);
                }
                self.eval_pure_call(func, &expr.ty, values, self.report_span())
            }
            TypedExprKind::Field { base, index, .. } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                self.project_field(value, &base.ty, *index, self.report_span())
            }
            TypedExprKind::TupleField { base, index } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                self.project_field(value, &base.ty, *index, self.report_span())
            }
            TypedExprKind::Deref { base } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                match &base.ty {
                    crate::spec::SpecTy::Ref(inner) => {
                        self.ref_deref(&value, inner, self.report_span())
                    }
                    crate::spec::SpecTy::Mut(inner) => {
                        self.mut_cur(&value, inner, self.report_span())
                    }
                    _ => unreachable!("typed deref base"),
                }
            }
            TypedExprKind::Fin { base } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                let SpecTy::Mut(inner) = &base.ty else {
                    unreachable!("typed fin base");
                };
                self.mut_fin(&value, inner, self.report_span())
            }
            TypedExprKind::Unary { op, arg } => {
                let value = self.contract_expr_to_value(current, spec, arg)?;
                Ok(self.lower_unary_value(*op, &value))
            }
            TypedExprKind::Binary { op, lhs, rhs } => {
                let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                self.lower_binary_value(*op, &lhs.ty, &lhs_value, &rhs_value, self.report_span())
            }
        }
    }

    fn eval_pure_call(
        &self,
        func: &str,
        result_ty: &SpecTy,
        values: Vec<SymValue>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let Some(pure_fn) = self.pure_fns.get(func) else {
            return Err(self.unsupported_result(span, format!("unknown pure function `{func}`")));
        };
        let decl = self.pure_fn_decl(pure_fn)?;
        self.apply_pure_fn_decl(&decl, result_ty, &values, span)
    }

    fn pure_fn_decl(&self, pure_fn: &TypedPureFnDef) -> Result<FuncDecl, VerificationResult> {
        let mut domain_sorts = Vec::with_capacity(pure_fn.params.len());
        for param in &pure_fn.params {
            domain_sorts.push(self.type_encoding(&param.ty)?.sort.clone());
        }
        let domain_refs: Vec<_> = domain_sorts.iter().collect();
        let result_sort = self.type_encoding(&pure_fn.result_ty)?.sort.clone();
        Ok(FuncDecl::new(
            format!("pure_fn_{}", pure_fn.name),
            &domain_refs,
            &result_sort,
        ))
    }

    fn apply_pure_fn_decl(
        &self,
        decl: &FuncDecl,
        result_ty: &SpecTy,
        values: &[SymValue],
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let args: Vec<&dyn Ast> = values.iter().map(sym_value_ast).collect();
        let app = decl.apply(&args);
        let encoding = self.type_encoding(result_ty)?;
        self.decode_value(&encoding, app, span)
    }

    fn function_postcondition_to_z3(
        &self,
        state: &State,
        contract: &FunctionContract,
    ) -> Result<Bool, VerificationResult> {
        let env = CallEnv::for_function(self, state, contract, self.function_spec_vars.clone())?;
        self.contract_ens_to_z3(contract, &env, self.report_span())
    }

    fn assert_constraint(
        &self,
        state: &mut State,
        constraint: Bool,
        kind: AssertionKind,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<(), VerificationResult> {
        match kind {
            AssertionKind::Universal => match self.check_sat(&[state.pc.clone(), constraint.not()])
            {
                SatResult::Sat => Err(VerificationResult {
                    function: self.report_function(),
                    status: VerificationStatus::Fail,
                    span: diagnostic_span,
                    message,
                }),
                SatResult::Unsat => {
                    self.add_path_condition(state, constraint);
                    Ok(())
                }
                SatResult::Unknown => Err(self.unknown_result(
                    span,
                    "solver returned unknown while checking assertion".to_owned(),
                )),
            },
            AssertionKind::Existential => {
                match self.check_sat(&[state.pc.clone(), constraint.clone()]) {
                    SatResult::Sat => {
                        self.add_path_condition(state, constraint);
                        Ok(())
                    }
                    SatResult::Unsat => Err(VerificationResult {
                        function: self.report_function(),
                        status: VerificationStatus::Fail,
                        span: diagnostic_span,
                        message,
                    }),
                    SatResult::Unknown => Err(self.unknown_result(
                        span,
                        "solver returned unknown while checking assertion".to_owned(),
                    )),
                }
            }
        }
    }

    fn assert_expr_constraint(
        &self,
        state: &mut State,
        expr: &TypedExpr,
        constraint: Bool,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<(), VerificationResult> {
        self.assert_constraint(
            state,
            constraint,
            Self::assertion_kind_for_expr(expr),
            span,
            diagnostic_span,
            message,
        )
    }

    fn assume_constraint(
        &self,
        state: &mut State,
        constraint: Bool,
        span: Span,
    ) -> Result<bool, VerificationResult> {
        match self.check_sat(&[state.pc.clone(), constraint.clone()]) {
            SatResult::Sat => {
                self.add_path_condition(state, constraint);
                Ok(true)
            }
            SatResult::Unsat => Ok(false),
            SatResult::Unknown => Err(self.unknown_result(
                span,
                "solver returned unknown while checking assumption".to_owned(),
            )),
        }
    }

    fn prune_state(
        &self,
        mut state: State,
        constraint: Bool,
        span: Span,
    ) -> Result<Option<State>, VerificationResult> {
        if self.assume_constraint(&mut state, constraint, span)? {
            Ok(Some(state))
        } else {
            Ok(None)
        }
    }

    fn add_path_condition(&self, state: &mut State, constraint: Bool) {
        state.pc = bool_and(vec![state.pc.clone(), constraint]);
    }

    fn check_sat(&self, assumptions: &[Bool]) -> SatResult {
        with_solver(|solver| {
            solver.push();
            for assumption in assumptions {
                solver.assert(assumption);
            }
            let result = solver.check();
            solver.pop(1);
            result
        })
    }

    fn bool_expr_to_z3(&self, expr: &BoolExpr) -> Result<Bool, VerificationResult> {
        match expr {
            BoolExpr::Const(value) => Ok(Bool::from_bool(*value)),
            BoolExpr::Value(value) => Ok(self.value_is_true(value)),
            BoolExpr::Not(arg) => Ok(self.bool_expr_to_z3(arg)?.not()),
        }
    }

    fn expr_has_bind(expr: &TypedExpr) -> bool {
        match &expr.kind {
            TypedExprKind::Bind(_) => true,
            TypedExprKind::Bool(_) | TypedExprKind::Int(_) | TypedExprKind::Var(_) => false,
            TypedExprKind::PureCall { args, .. } => args.iter().any(Self::expr_has_bind),
            TypedExprKind::Field { base, .. }
            | TypedExprKind::TupleField { base, .. }
            | TypedExprKind::Deref { base }
            | TypedExprKind::Fin { base }
            | TypedExprKind::Unary { arg: base, .. } => Self::expr_has_bind(base),
            TypedExprKind::Binary { lhs, rhs, .. } => {
                Self::expr_has_bind(lhs) || Self::expr_has_bind(rhs)
            }
        }
    }

    fn assertion_kind_for_expr(expr: &TypedExpr) -> AssertionKind {
        if Self::expr_has_bind(expr) {
            AssertionKind::Existential
        } else {
            AssertionKind::Universal
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
                let inner = match ty.kind() {
                    TyKind::Ref(_, inner, _) => *inner,
                    _ => unreachable!(),
                };
                let updated = self.abstract_mut_ref(&current, inner, span)?;
                self.write_place(state, place, updated, span)?;
            }
        }
        Ok(())
    }

    fn consume_call_move_args(
        &self,
        state: &mut State,
        args: &[Spanned<Operand<'tcx>>],
        span: Span,
    ) -> Result<(), VerificationResult> {
        for arg in args {
            self.consume_operand(state, &arg.node, span)?;
        }
        Ok(())
    }

    fn abstract_mut_ref(
        &self,
        value: &SymValue,
        inner_ty: Ty<'tcx>,
        _span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let inner_spec_ty = self.spec_ty_for_place_ty(inner_ty, self.report_span())?;
        let final_value = self.mut_fin(value, &inner_spec_ty, self.report_span())?;
        let fresh = self.fresh_for_rust_ty(inner_ty, "opaque_cur")?;
        self.construct_datatype(&SpecTy::Mut(Box::new(inner_spec_ty)), &[fresh, final_value])
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
            let ty = self.body().local_decls[*local].ty;
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

    fn is_immediate_return_block(&self, block: BasicBlock) -> bool {
        let data = &self.body().basic_blocks[block];
        data.statements.is_empty() && matches!(data.terminator().kind, TerminatorKind::Return)
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

    fn missing_local_contract_result(&self, def_id: LocalDefId, span: Span) -> VerificationResult {
        let callee = self.tcx.def_path_str(def_id.to_def_id());
        self.unsupported_result(
            span,
            format!("missing local function contract for `{callee}`"),
        )
    }

    fn place_ty(&self, place: Place<'tcx>) -> Ty<'tcx> {
        place.ty(&self.body().local_decls, self.tcx).ty
    }

    fn is_reborrow(&self, place: Place<'tcx>) -> bool {
        place
            .as_ref()
            .projection
            .iter()
            .any(|elem| matches!(elem, PlaceElem::Deref))
    }

    fn control_span(&self, ctrl: ControlPoint) -> Span {
        let data = &self.body().basic_blocks[ctrl.basic_block];
        if ctrl.statement_index < data.statements.len() {
            data.statements[ctrl.statement_index].source_info.span
        } else {
            data.terminator().source_info.span
        }
    }

    fn value_int(&self, value: i64) -> SymValue {
        self.value_wrap_int(&Int::from_i64(value))
    }

    fn value_decimal_int(&self, digits: &str, span: Span) -> Result<SymValue, VerificationResult> {
        let int = Int::from_str(digits).map_err(|()| {
            self.unsupported_result(span, format!("invalid integer literal `{digits}`"))
        })?;
        Ok(self.value_wrap_int(&int))
    }

    fn value_bool(&self, value: bool) -> SymValue {
        self.value_wrap_bool(&Bool::from_bool(value))
    }

    fn value_wrap_bool(&self, value: &Bool) -> SymValue {
        let encoding = self
            .type_encoding(&SpecTy::Bool)
            .expect("bool encoding should be available");
        let TypeEncodingKind::Bool(encoding) = &encoding.kind else {
            unreachable!("bool encoding kind");
        };
        SymValue::Bool(PrimitiveValue {
            ast: encoding.boxed.apply(&[value]),
            data: value.clone(),
        })
    }

    fn value_wrap_int(&self, value: &Int) -> SymValue {
        let encoding = self
            .type_encoding(&SpecTy::IntLiteral)
            .expect("int encoding should be available");
        let TypeEncodingKind::Int(encoding) = &encoding.kind else {
            unreachable!("int encoding kind");
        };
        SymValue::Int(PrimitiveValue {
            ast: encoding.boxed.apply(&[value]),
            data: value.clone(),
        })
    }

    fn value_is_true(&self, value: &SymValue) -> Bool {
        match value {
            SymValue::Bool(value) => value.data.clone(),
            _ => unreachable!("typed bool expression lowered to non-bool value"),
        }
    }

    fn value_int_data(&self, value: &SymValue) -> Int {
        match value {
            SymValue::Int(value) => value.data.clone(),
            _ => unreachable!("typed int expression lowered to non-int value"),
        }
    }

    fn value_bool_data(&self, value: &SymValue) -> Bool {
        match value {
            SymValue::Bool(value) => value.data.clone(),
            _ => unreachable!("typed bool expression lowered to non-bool value"),
        }
    }

    fn eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let encoding = self.type_encoding(ty)?;
        self.eq_for_encoding(&encoding, lhs, rhs, span)
    }

    fn eq_for_encoding(
        &self,
        encoding: &TypeEncoding,
        lhs: &SymValue,
        rhs: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match &encoding.kind {
            TypeEncodingKind::Bool(primitive) => Ok(self
                .decode_bool_payload(primitive, sym_value_dynamic(lhs), span)?
                .eq(self.decode_bool_payload(primitive, sym_value_dynamic(rhs), span)?)),
            TypeEncodingKind::Int(primitive) => Ok(self
                .decode_int_payload(primitive, sym_value_dynamic(lhs), span)?
                .eq(self.decode_int_payload(primitive, sym_value_dynamic(rhs), span)?)),
            TypeEncodingKind::Inductive(_) => Ok(sym_value_dynamic(lhs).eq(sym_value_dynamic(rhs))),
        }
    }

    fn lower_unary_value(&self, op: UnaryOp, value: &SymValue) -> SymValue {
        match op {
            UnaryOp::Not => self.value_wrap_bool(&self.value_bool_data(value).not()),
            UnaryOp::Neg => self.value_wrap_int(&(Int::from_i64(0) - self.value_int_data(value))),
        }
    }

    fn lower_binary_value(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        Ok(match op {
            BinaryOp::Eq => self.value_wrap_bool(&self.eq_for_spec_ty(lhs_ty, lhs, rhs, span)?),
            BinaryOp::Ne => {
                self.value_wrap_bool(&self.eq_for_spec_ty(lhs_ty, lhs, rhs, span)?.not())
            }
            BinaryOp::And => self.value_wrap_bool(&Bool::and(&[
                &self.value_bool_data(lhs),
                &self.value_bool_data(rhs),
            ])),
            BinaryOp::Or => self.value_wrap_bool(&Bool::or(&[
                &self.value_bool_data(lhs),
                &self.value_bool_data(rhs),
            ])),
            BinaryOp::Lt => {
                self.value_wrap_bool(&self.value_int_data(lhs).lt(self.value_int_data(rhs)))
            }
            BinaryOp::Le => {
                self.value_wrap_bool(&self.value_int_data(lhs).le(self.value_int_data(rhs)))
            }
            BinaryOp::Gt => {
                self.value_wrap_bool(&self.value_int_data(lhs).gt(self.value_int_data(rhs)))
            }
            BinaryOp::Ge => {
                self.value_wrap_bool(&self.value_int_data(lhs).ge(self.value_int_data(rhs)))
            }
            BinaryOp::Add => {
                self.value_wrap_int(&(self.value_int_data(lhs) + self.value_int_data(rhs)))
            }
            BinaryOp::Sub => {
                self.value_wrap_int(&(self.value_int_data(lhs) - self.value_int_data(rhs)))
            }
            BinaryOp::Mul => {
                self.value_wrap_int(&(self.value_int_data(lhs) * self.value_int_data(rhs)))
            }
        })
    }

    fn type_encoding(&self, ty: &SpecTy) -> Result<Rc<TypeEncoding>, VerificationResult> {
        with_solver(|solver| self.value_encoder.type_encoding(ty, solver))
            .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn datatype_encoding(&self, ty: &SpecTy) -> Result<Rc<InductiveEncoding>, VerificationResult> {
        with_solver(|solver| self.value_encoder.inductive_encoding(ty, solver))
            .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn construct_datatype(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.datatype_encoding(ty)?;
        let asts = fields.iter().map(sym_value_ast).collect::<Vec<_>>();
        Ok(SymValue::Inductive(InductiveValue {
            ast: encoding.constructor.apply(&asts),
        }))
    }

    fn decode_value(
        &self,
        encoding: &TypeEncoding,
        value: Dynamic,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match &encoding.kind {
            TypeEncodingKind::Bool(encoding) => Ok(SymValue::Bool(PrimitiveValue {
                ast: value.clone(),
                data: self.decode_bool_payload(encoding, &value, span)?,
            })),
            TypeEncodingKind::Int(encoding) => Ok(SymValue::Int(PrimitiveValue {
                ast: value.clone(),
                data: self.decode_int_payload(encoding, &value, span)?,
            })),
            TypeEncodingKind::Inductive(_) => {
                Ok(SymValue::Inductive(InductiveValue { ast: value }))
            }
        }
    }

    fn decode_bool_payload(
        &self,
        encoding: &crate::value_encoding::PrimitiveEncoding,
        value: &Dynamic,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        if let Some(payload) = self.boxed_payload(value, &encoding.boxed_name) {
            return payload.as_bool().ok_or_else(|| {
                self.unsupported_result(span, "expected boxed bool payload".to_owned())
            });
        }
        encoding
            .unboxed
            .apply(&[value])
            .as_bool()
            .ok_or_else(|| self.unsupported_result(span, "expected boxed bool value".to_owned()))
    }

    fn decode_int_payload(
        &self,
        encoding: &crate::value_encoding::PrimitiveEncoding,
        value: &Dynamic,
        span: Span,
    ) -> Result<Int, VerificationResult> {
        if let Some(payload) = self.boxed_payload(value, &encoding.boxed_name) {
            return payload.as_int().ok_or_else(|| {
                self.unsupported_result(span, "expected boxed int payload".to_owned())
            });
        }
        encoding
            .unboxed
            .apply(&[value])
            .as_int()
            .ok_or_else(|| self.unsupported_result(span, "expected boxed int value".to_owned()))
    }

    fn boxed_payload(&self, value: &Dynamic, boxed_name: &str) -> Option<Dynamic> {
        if value.decl().name() != boxed_name {
            return None;
        }
        let children = value.children();
        (children.len() == 1).then(|| children[0].clone())
    }

    fn fresh_for_rust_ty(&self, ty: Ty<'tcx>, hint: &str) -> Result<SymValue, VerificationResult> {
        let spec_ty = spec_ty_for_rust_ty(self.tcx, ty)
            .map_err(|err| self.unsupported_result(self.report_span(), err))?;
        if let TyKind::Adt(adt_def, args) = ty.kind() {
            debug_assert!(adt_def.is_struct());
            debug_assert!(args.is_empty());
            if adt_def.has_dtor(self.tcx) {
                return Err(self.unsupported_result(
                    self.report_span(),
                    format!("structs with Drop are unsupported: {ty:?}"),
                ));
            }
        }
        self.fresh_for_spec_ty(&spec_ty, hint)
    }

    fn fresh_for_spec_ty(&self, ty: &SpecTy, hint: &str) -> Result<SymValue, VerificationResult> {
        let encoding = self.type_encoding(ty)?;
        self.fresh_for_encoding(&encoding, hint)
    }

    fn fresh_for_encoding(
        &self,
        encoding: &TypeEncoding,
        hint: &str,
    ) -> Result<SymValue, VerificationResult> {
        match &encoding.kind {
            TypeEncodingKind::Bool(_) => {
                Ok(self.value_wrap_bool(&Bool::new_const(self.fresh_name(hint))))
            }
            TypeEncodingKind::Int(_) => {
                Ok(self.value_wrap_int(&Int::new_const(self.fresh_name(hint))))
            }
            TypeEncodingKind::Inductive(inductive) => {
                let mut fields = Vec::with_capacity(inductive.fields.len());
                for (index, field_encoding) in inductive.fields.iter().enumerate() {
                    fields.push(self.fresh_for_encoding(
                        field_encoding,
                        &format!("{hint}_{}", inductive.field_labels[index]),
                    )?);
                }
                let asts = fields.iter().map(sym_value_ast).collect::<Vec<_>>();
                Ok(SymValue::Inductive(InductiveValue {
                    ast: inductive.constructor.apply(&asts),
                }))
            }
        }
    }

    fn project_field(
        &self,
        value: SymValue,
        parent_ty: &SpecTy,
        index: usize,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.datatype_encoding(parent_ty)?;
        self.project_field_from_encoding(value, &encoding, index, span)
    }

    fn project_field_from_encoding(
        &self,
        value: SymValue,
        encoding: &InductiveEncoding,
        index: usize,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let SymValue::Inductive(value) = value else {
            return Err(self.unsupported_result(
                span,
                "field projection requires datatype-backed value".to_owned(),
            ));
        };
        let field = encoding
            .fields
            .get(index)
            .ok_or_else(|| self.unsupported_result(span, "field index out of range".to_owned()))?;
        if let Some(payload) = self.constructor_field(&value.ast, encoding, index) {
            return self.decode_value(field, payload, span);
        }
        self.decode_value(field, encoding.accessors[index].apply(&[&value.ast]), span)
    }

    fn ref_deref(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        if !matches!(value, SymValue::Inductive(_)) {
            return Err(self.unsupported_result(span, "expected shared reference value".to_owned()));
        }
        let encoding = self.datatype_encoding(&SpecTy::Ref(Box::new(inner_ty.clone())))?;
        self.decode_inductive_field(&encoding, value, 0, span)
    }

    fn mut_cur(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        if !matches!(value, SymValue::Inductive(_)) {
            return Err(
                self.unsupported_result(span, "expected mutable reference value".to_owned())
            );
        }
        let encoding = self.datatype_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_inductive_field(&encoding, value, 0, span)
    }

    fn mut_fin(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        if !matches!(value, SymValue::Inductive(_)) {
            return Err(
                self.unsupported_result(span, "expected mutable reference value".to_owned())
            );
        }
        let encoding = self.datatype_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_inductive_field(&encoding, value, 1, span)
    }

    fn spec_ty_for_place_ty(&self, ty: Ty<'tcx>, span: Span) -> Result<SpecTy, VerificationResult> {
        spec_ty_for_rust_ty(self.tcx, ty).map_err(|err| self.unsupported_result(span, err))
    }

    fn deref_spec_ty<'a>(&self, ty: &'a SpecTy) -> Option<&'a SpecTy> {
        match ty {
            SpecTy::Ref(inner) | SpecTy::Mut(inner) => Some(inner.as_ref()),
            _ => None,
        }
    }

    fn composite_spec_field_count(&self, ty: &SpecTy) -> Option<usize> {
        match ty {
            SpecTy::Tuple(items) => Some(items.len()),
            SpecTy::Struct(struct_ty) => Some(struct_ty.fields.len()),
            _ => None,
        }
    }

    fn composite_spec_field_ty<'a>(&self, ty: &'a SpecTy, index: usize) -> Option<&'a SpecTy> {
        match ty {
            SpecTy::Tuple(items) => items.get(index),
            SpecTy::Struct(struct_ty) => struct_ty.fields.get(index).map(|field| &field.ty),
            _ => None,
        }
    }

    fn fresh_name(&self, hint: &str) -> String {
        let id = self.next_sym.get();
        self.next_sym.set(id + 1);
        format!("{hint}_{id}")
    }

    fn adt_field_tys(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Vec<Ty<'tcx>> {
        adt_def
            .non_enum_variant()
            .fields
            .iter()
            .map(|field| field.ty(self.tcx, args))
            .collect()
    }

    fn ty_contains_mut_ref(&self, ty: Ty<'tcx>) -> bool {
        spec_ty_for_rust_ty(self.tcx, ty)
            .map(|ty| spec_ty_contains_mut_ref(&ty))
            .unwrap_or(matches!(ty.kind(), TyKind::Ref(_, _, mutability) if mutability.is_mut()))
    }

    fn int_bounds_for_rust_ty(
        &self,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<Option<(Int, Int)>, VerificationResult> {
        Ok(Some(match ty.kind() {
            TyKind::Int(kind) => match kind {
                ty::IntTy::I8 => (Int::from_i64(i8::MIN.into()), Int::from_i64(i8::MAX.into())),
                ty::IntTy::I16 => (
                    Int::from_i64(i16::MIN.into()),
                    Int::from_i64(i16::MAX.into()),
                ),
                ty::IntTy::I32 => (
                    Int::from_i64(i32::MIN.into()),
                    Int::from_i64(i32::MAX.into()),
                ),
                ty::IntTy::I64 => (Int::from_i64(i64::MIN), Int::from_i64(i64::MAX)),
                ty::IntTy::Isize => self.pointer_sized_int_bounds(true)?,
                other => {
                    return Err(self
                        .unsupported_result(span, format!("unsupported integer type {other:?}")));
                }
            },
            TyKind::Uint(kind) => match kind {
                ty::UintTy::U8 => (Int::from_u64(0), Int::from_u64(u8::MAX.into())),
                ty::UintTy::U16 => (Int::from_u64(0), Int::from_u64(u16::MAX.into())),
                ty::UintTy::U32 => (Int::from_u64(0), Int::from_u64(u32::MAX.into())),
                ty::UintTy::U64 => (Int::from_u64(0), Int::from_u64(u64::MAX)),
                ty::UintTy::Usize => self.pointer_sized_int_bounds(false)?,
                other => {
                    return Err(self
                        .unsupported_result(span, format!("unsupported integer type {other:?}")));
                }
            },
            _ => return Ok(None),
        }))
    }

    fn int_bounds_for_spec_ty(
        &self,
        ty: &SpecTy,
        span: Span,
    ) -> Result<Option<(Int, Int)>, VerificationResult> {
        let rust_ty = match ty {
            SpecTy::I8 => Some(self.tcx.types.i8),
            SpecTy::I16 => Some(self.tcx.types.i16),
            SpecTy::I32 => Some(self.tcx.types.i32),
            SpecTy::I64 => Some(self.tcx.types.i64),
            SpecTy::Isize => Some(self.tcx.types.isize),
            SpecTy::U8 => Some(self.tcx.types.u8),
            SpecTy::U16 => Some(self.tcx.types.u16),
            SpecTy::U32 => Some(self.tcx.types.u32),
            SpecTy::U64 => Some(self.tcx.types.u64),
            SpecTy::Usize => Some(self.tcx.types.usize),
            _ => None,
        };
        rust_ty
            .map(|rust_ty| self.int_bounds_for_rust_ty(rust_ty, span))
            .transpose()
            .map(|opt| opt.flatten())
    }

    fn int_range_formula_for_int(&self, bounds: Option<(Int, Int)>, value: &Int) -> Option<Bool> {
        bounds.map(|(lower, upper)| bool_and(vec![value.ge(lower), value.le(upper)]))
    }

    fn pointer_sized_int_bounds(&self, signed: bool) -> Result<(Int, Int), VerificationResult> {
        let bits = self.tcx.data_layout.pointer_size().bits();
        if signed {
            let lower = -(1_i128 << (bits - 1));
            let upper = (1_i128 << (bits - 1)) - 1;
            let lower = Int::from_str(&lower.to_string()).map_err(|()| {
                self.unsupported_result(self.report_span(), "invalid isize lower bound".to_owned())
            })?;
            let upper = Int::from_str(&upper.to_string()).map_err(|()| {
                self.unsupported_result(self.report_span(), "invalid isize upper bound".to_owned())
            })?;
            Ok((lower, upper))
        } else {
            let upper = (1_u128 << bits) - 1;
            let upper = Int::from_str(&upper.to_string()).map_err(|()| {
                self.unsupported_result(self.report_span(), "invalid usize upper bound".to_owned())
            })?;
            Ok((Int::from_u64(0), upper))
        }
    }

    fn scalar_int_to_value(
        &self,
        ty: Ty<'tcx>,
        value: ty::ScalarInt,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let int = match ty.kind() {
            TyKind::Int(kind) => match kind {
                ty::IntTy::I8 => Int::from_i64(value.to_i8().into()),
                ty::IntTy::I16 => Int::from_i64(value.to_i16().into()),
                ty::IntTy::I32 => Int::from_i64(value.to_i32().into()),
                ty::IntTy::I64 => Int::from_i64(value.to_i64()),
                ty::IntTy::Isize => Int::from_str(&value.to_target_isize(self.tcx).to_string())
                    .map_err(|()| {
                        self.unsupported_result(
                            span,
                            format!("failed to evaluate integer constant for {ty:?}"),
                        )
                    })?,
                _ => {
                    return Err(
                        self.unsupported_result(span, format!("unsupported integer type {ty:?}"))
                    );
                }
            },
            TyKind::Uint(kind) => match kind {
                ty::UintTy::U8 => Int::from_u64(value.to_u8().into()),
                ty::UintTy::U16 => Int::from_u64(value.to_u16().into()),
                ty::UintTy::U32 => Int::from_u64(value.to_u32().into()),
                ty::UintTy::U64 => Int::from_u64(value.to_u64()),
                ty::UintTy::Usize => Int::from_str(&value.to_target_usize(self.tcx).to_string())
                    .map_err(|()| {
                        self.unsupported_result(
                            span,
                            format!("failed to evaluate integer constant for {ty:?}"),
                        )
                    })?,
                _ => {
                    return Err(
                        self.unsupported_result(span, format!("unsupported integer type {ty:?}"))
                    );
                }
            },
            _ => {
                return Err(
                    self.unsupported_result(span, format!("expected integer type, found {ty:?}"))
                );
            }
        };
        Ok(self.value_wrap_int(&int))
    }

    fn overflow_value_for_result(
        &self,
        ty: Ty<'tcx>,
        value: &SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let in_range = self
            .int_range_formula_for_int(
                self.int_bounds_for_rust_ty(ty, span)?,
                &self.value_int_data(value),
            )
            .unwrap_or_else(|| Bool::from_bool(true));
        Ok(self.value_wrap_bool(&bool_not(in_range)))
    }

    fn int_range_formula_for_spec_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<Bool>, VerificationResult> {
        Ok(self.int_range_formula_for_int(
            self.int_bounds_for_spec_ty(ty, span)?,
            &self.value_int_data(value),
        ))
    }

    fn spec_ty_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<Bool>, VerificationResult> {
        let encoding = self.type_encoding(ty)?;
        self.spec_ty_formula_for_encoding(ty, &encoding, value, span)
    }

    fn spec_ty_formula_for_encoding(
        &self,
        ty: &SpecTy,
        encoding: &TypeEncoding,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<Bool>, VerificationResult> {
        match (&encoding.kind, ty) {
            (TypeEncodingKind::Bool(_), SpecTy::Bool) => Ok(None),
            (TypeEncodingKind::Int(_), SpecTy::IntLiteral) => Ok(None),
            (
                TypeEncodingKind::Int(_),
                SpecTy::I8
                | SpecTy::I16
                | SpecTy::I32
                | SpecTy::I64
                | SpecTy::Isize
                | SpecTy::U8
                | SpecTy::U16
                | SpecTy::U32
                | SpecTy::U64
                | SpecTy::Usize,
            ) => self.int_range_formula_for_spec_ty(ty, value, span),
            (TypeEncodingKind::Inductive(inductive), SpecTy::Ref(inner)) => {
                let mut formulas =
                    vec![self.inductive_tag_formula_for_encoding(inductive, value, span)?];
                let deref_value = self.decode_inductive_field(inductive, value, 0, span)?;
                if let Some(formula) = self.spec_ty_formula_for_encoding(
                    inner,
                    &inductive.fields[0],
                    &deref_value,
                    span,
                )? {
                    formulas.push(formula);
                }
                Ok(Some(bool_and(formulas)))
            }
            (TypeEncodingKind::Inductive(inductive), SpecTy::Mut(inner)) => {
                let mut formulas =
                    vec![self.inductive_tag_formula_for_encoding(inductive, value, span)?];
                let current = self.decode_inductive_field(inductive, value, 0, span)?;
                if let Some(formula) =
                    self.spec_ty_formula_for_encoding(inner, &inductive.fields[0], &current, span)?
                {
                    formulas.push(formula);
                }
                Ok(Some(bool_and(formulas)))
            }
            (TypeEncodingKind::Inductive(inductive), SpecTy::Tuple(items)) => {
                let mut formulas =
                    vec![self.inductive_tag_formula_for_encoding(inductive, value, span)?];
                for (index, item) in items.iter().enumerate() {
                    let field = self.decode_inductive_field(inductive, value, index, span)?;
                    if let Some(formula) = self.spec_ty_formula_for_encoding(
                        item,
                        &inductive.fields[index],
                        &field,
                        span,
                    )? {
                        formulas.push(formula);
                    }
                }
                Ok(Some(bool_and(formulas)))
            }
            (TypeEncodingKind::Inductive(inductive), SpecTy::Struct(struct_ty)) => {
                let mut formulas =
                    vec![self.inductive_tag_formula_for_encoding(inductive, value, span)?];
                for (index, field_ty) in struct_ty.fields.iter().enumerate() {
                    let field = self.decode_inductive_field(inductive, value, index, span)?;
                    if let Some(formula) = self.spec_ty_formula_for_encoding(
                        &field_ty.ty,
                        &inductive.fields[index],
                        &field,
                        span,
                    )? {
                        formulas.push(formula);
                    }
                }
                Ok(Some(bool_and(formulas)))
            }
            _ => Err(self.unsupported_result(
                span,
                format!("type/encoding mismatch for invariant: {ty:?}"),
            )),
        }
    }

    fn resolve_formula_for_spec_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let encoding = self.type_encoding(ty)?;
        self.resolve_formula_for_encoding(ty, &encoding, value, span)
    }

    fn resolve_formula_for_encoding(
        &self,
        ty: &SpecTy,
        encoding: &TypeEncoding,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match (&encoding.kind, ty) {
            (
                TypeEncodingKind::Bool(_) | TypeEncodingKind::Int(_),
                SpecTy::Bool
                | SpecTy::IntLiteral
                | SpecTy::I8
                | SpecTy::I16
                | SpecTy::I32
                | SpecTy::I64
                | SpecTy::Isize
                | SpecTy::U8
                | SpecTy::U16
                | SpecTy::U32
                | SpecTy::U64
                | SpecTy::Usize,
            ) => Ok(Bool::from_bool(true)),
            (TypeEncodingKind::Inductive(inductive), SpecTy::Ref(_)) => {
                self.inductive_tag_formula_for_encoding(inductive, value, span)
            }
            (TypeEncodingKind::Inductive(inductive), SpecTy::Mut(inner)) => {
                let cur = self.decode_inductive_field(inductive, value, 0, span)?;
                let fin = self.decode_inductive_field(inductive, value, 1, span)?;
                Ok(bool_and(vec![
                    self.inductive_tag_formula_for_encoding(inductive, value, span)?,
                    self.eq_for_encoding(&inductive.fields[0], &cur, &fin, span)?,
                    self.resolve_formula_for_encoding(inner, &inductive.fields[0], &cur, span)?,
                    self.resolve_formula_for_encoding(inner, &inductive.fields[1], &fin, span)?,
                ]))
            }
            (TypeEncodingKind::Inductive(inductive), SpecTy::Tuple(items)) => {
                let mut formulas = Vec::with_capacity(items.len() + 1);
                formulas.push(self.inductive_tag_formula_for_encoding(inductive, value, span)?);
                for (index, item) in items.iter().enumerate() {
                    let field = self.decode_inductive_field(inductive, value, index, span)?;
                    formulas.push(self.resolve_formula_for_encoding(
                        item,
                        &inductive.fields[index],
                        &field,
                        span,
                    )?);
                }
                Ok(bool_and(formulas))
            }
            (TypeEncodingKind::Inductive(inductive), SpecTy::Struct(struct_ty)) => {
                let mut formulas = Vec::with_capacity(struct_ty.fields.len() + 1);
                formulas.push(self.inductive_tag_formula_for_encoding(inductive, value, span)?);
                for (index, field_ty) in struct_ty.fields.iter().enumerate() {
                    let field = self.decode_inductive_field(inductive, value, index, span)?;
                    formulas.push(self.resolve_formula_for_encoding(
                        &field_ty.ty,
                        &inductive.fields[index],
                        &field,
                        span,
                    )?);
                }
                Ok(bool_and(formulas))
            }
            _ => Err(self.unsupported_result(
                span,
                format!("type/encoding mismatch for resolution: {ty:?}"),
            )),
        }
    }

    fn decode_inductive_field(
        &self,
        encoding: &InductiveEncoding,
        value: &SymValue,
        index: usize,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let SymValue::Inductive(value) = value else {
            return Err(self.unsupported_result(span, "expected datatype-backed value".to_owned()));
        };
        let field_encoding = encoding
            .fields
            .get(index)
            .ok_or_else(|| self.unsupported_result(span, "field index out of range".to_owned()))?;
        if let Some(payload) = self.constructor_field(&value.ast, encoding, index) {
            return self.decode_value(field_encoding, payload, span);
        }
        self.decode_value(
            field_encoding,
            encoding.accessors[index].apply(&[&value.ast]),
            span,
        )
    }

    fn constructor_field(
        &self,
        value: &Dynamic,
        encoding: &InductiveEncoding,
        index: usize,
    ) -> Option<Dynamic> {
        if value.decl().name() != encoding.constructor_name {
            return None;
        }
        value.children().get(index).cloned()
    }

    fn inductive_tag_formula_for_encoding(
        &self,
        encoding: &InductiveEncoding,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let SymValue::Inductive(value) = value else {
            return Err(self.unsupported_result(span, "expected datatype-backed value".to_owned()));
        };
        if value.ast.decl().name() == encoding.constructor_name {
            return Ok(Bool::from_bool(true));
        }
        Ok(self
            .value_encoder
            .tag_function()
            .apply(&[&value.ast])
            .as_int()
            .expect("tag result")
            .eq(&encoding.tag))
    }

    fn require_type_invariant(
        &self,
        state: &mut State,
        ty: Ty<'tcx>,
        value: &SymValue,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let spec_ty =
            spec_ty_for_rust_ty(self.tcx, ty).map_err(|err| self.unsupported_result(span, err))?;
        let Some(formula) = self.spec_ty_formula(&spec_ty, value, span)? else {
            return Ok(());
        };
        self.assert_constraint(
            state,
            formula,
            AssertionKind::Universal,
            span,
            span_text(self.tcx, span),
            message,
        )
    }

    fn require_int_invariant(
        &self,
        state: &mut State,
        ty: Ty<'tcx>,
        value: &Int,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let Some((lower, upper)) = self.int_bounds_for_rust_ty(ty, span)? else {
            return Ok(());
        };
        self.assert_constraint(
            state,
            bool_and(vec![value.ge(lower), value.le(upper)]),
            AssertionKind::Universal,
            span,
            span_text(self.tcx, span),
            message,
        )
    }

    fn unsupported_result(&self, span: Span, message: String) -> VerificationResult {
        VerificationResult {
            function: self.report_function(),
            status: VerificationStatus::Unsupported,
            span: span_text(self.tcx, span),
            message,
        }
    }

    fn unknown_result(&self, span: Span, message: String) -> VerificationResult {
        VerificationResult {
            function: self.report_function(),
            status: VerificationStatus::Unknown,
            span: span_text(self.tcx, span),
            message,
        }
    }

    fn pass_result(&self, message: &str) -> VerificationResult {
        VerificationResult {
            function: self.report_function(),
            status: VerificationStatus::Pass,
            span: span_text(self.tcx, self.report_span()),
            message: message.to_owned(),
        }
    }

    fn call_env(
        &self,
        state: &State,
        args: &[Spanned<Operand<'tcx>>],
        contract: &FunctionContract,
        span: Span,
        spec: HashMap<String, SymValue>,
    ) -> Result<CallEnv, VerificationResult> {
        let mut current = HashMap::new();
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
        for (param, arg) in contract.params.iter().zip(args.iter()) {
            let value = self.read_operand(state, &arg.node, span)?;
            current.insert(param.name.clone(), value.clone());
        }
        Ok(CallEnv { current, spec })
    }

    fn instantiate_contract_spec_vars(
        &self,
        contract: &FunctionContract,
    ) -> HashMap<String, SymValue> {
        self.instantiate_spec_vars(&contract.spec_vars)
    }

    fn instantiate_spec_vars(&self, spec_vars: &[SpecVarBinding]) -> HashMap<String, SymValue> {
        let mut spec = HashMap::new();
        for binding in spec_vars {
            let symbol = format!("spec_{}", self.fresh_name(&binding.name));
            let value = self
                .fresh_for_spec_ty(&binding.ty, &symbol)
                .expect("spec variable instantiation must succeed");
            spec.insert(binding.name.clone(), value);
        }
        spec
    }

    fn contract_req_to_z3(
        &self,
        contract: &FunctionContract,
        env: &CallEnv,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        self.contract_side_to_z3(contract, env, span, false)
    }

    fn contract_ens_to_z3(
        &self,
        contract: &FunctionContract,
        env: &CallEnv,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        self.contract_side_to_z3(contract, env, span, true)
    }

    fn contract_side_to_z3(
        &self,
        contract: &FunctionContract,
        env: &CallEnv,
        span: Span,
        is_post: bool,
    ) -> Result<Bool, VerificationResult> {
        let manual = if is_post {
            self.contract_expr_to_bool(&env.current, &env.spec, &contract.ens)?
        } else {
            self.contract_expr_to_bool(&env.current, &env.spec, &contract.req)?
        };
        let mut formulas = vec![self.bool_expr_to_z3(&manual)?];
        formulas.extend(self.auto_contract_formulas(contract, env, span, is_post)?);
        Ok(bool_and(formulas))
    }

    fn auto_contract_formulas(
        &self,
        contract: &FunctionContract,
        env: &CallEnv,
        span: Span,
        is_post: bool,
    ) -> Result<Vec<Bool>, VerificationResult> {
        if is_post {
            let Some(result) = env.current.get("result") else {
                return Ok(Vec::new());
            };
            let Some(formula) = self.spec_ty_formula(&contract.result, result, span)? else {
                return Ok(Vec::new());
            };
            return Ok(vec![formula]);
        }
        let mut formulas = Vec::new();
        for ContractParam { name, ty } in &contract.params {
            let value = env.current.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(span, format!("missing contract binding `{name}`"))
            })?;
            if let Some(formula) = self.spec_ty_formula(ty, &value, span)? {
                formulas.push(formula);
            }
        }
        Ok(formulas)
    }
}

#[derive(Debug, Clone, Copy)]
enum ReadMode {
    Current,
    Final,
}

#[derive(Debug, Clone)]
struct CallEnv {
    current: HashMap<String, SymValue>,
    spec: HashMap<String, SymValue>,
}

impl CallEnv {
    fn for_function<'tcx>(
        verifier: &Verifier<'tcx>,
        state: &State,
        contract: &FunctionContract,
        spec: HashMap<String, SymValue>,
    ) -> Result<Self, VerificationResult> {
        let mut current = HashMap::new();
        for (param, local) in contract
            .params
            .iter()
            .zip(verifier.body().local_decls.indices().skip(1))
        {
            let value = state.model.get(&local).cloned().ok_or_else(|| {
                verifier.unsupported_result(
                    verifier.control_span(state.ctrl),
                    format!("missing local {}", local.as_usize()),
                )
            })?;
            current.insert(param.name.clone(), value);
        }
        if let Some(result) = state.model.get(&Local::from_usize(0)).cloned() {
            current.insert("result".to_owned(), result);
        }
        Ok(Self { current, spec })
    }
}

fn init_z3() {
    Z3_INIT.call_once(|| {
        z3::set_global_param("model", "true");
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");
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

fn spec_ty_contains_mut_ref(ty: &SpecTy) -> bool {
    match ty {
        SpecTy::Mut(_) => true,
        SpecTy::Ref(inner) => spec_ty_contains_mut_ref(inner),
        SpecTy::Tuple(items) => items.iter().any(spec_ty_contains_mut_ref),
        SpecTy::Struct(struct_ty) => struct_ty
            .fields
            .iter()
            .any(|field| spec_ty_contains_mut_ref(&field.ty)),
        _ => false,
    }
}

fn span_text(tcx: TyCtxt<'_>, span: Span) -> String {
    tcx.sess.source_map().span_to_diagnostic_string(span)
}

fn sym_value_dynamic(value: &SymValue) -> &Dynamic {
    match value {
        SymValue::Bool(value) => &value.ast,
        SymValue::Int(value) => &value.ast,
        SymValue::Inductive(value) => &value.ast,
    }
}

fn sym_value_ast(value: &SymValue) -> &dyn Ast {
    sym_value_dynamic(value)
}
