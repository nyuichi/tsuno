#![allow(clippy::result_large_err)]

// Supported Rust types are reflected into the spec language and encoded in Z3 as follows:
//
// | Rust type                          | spec type           | Z3 representation | invariant |
// | ---------------------------------- | ------------------- | ----------------- | --------- |
// | `bool`                             | `bool`              | `Bool`            | `true` |
// | `i8`, `i16`, `i32`, `i64`, `isize` | same as Rust        | `Int`             | width bounds |
// | `u8`, `u16`, `u32`, `u64`, `usize` | same as Rust        | `Int`             | width bounds |
// | `&T`                               | `Ref<T>`            | datatype wrapper  | `inv<T>(deref(x))` |
// | `&mut T`                           | `Mut<T>`            | datatype wrapper  | `inv<T>(cur(x))` |
// | `Vec<T>`                           | `Seq<T>`            | `Seq<T>`          | each element satisfies `inv<T>` |
// | `(T0, .., Tn)`                     | `Tuple([T0, .., Tn])` | datatype        | conjunction of field invariants |
// | `struct S { f0: T0, .., fn: Tn }`  | `S`                 | datatype          | conjunction of field invariants |
//
// Notes:
// - `Mut<T>` additionally requires `cur(x) == fin(x)` when the mutable reference is closed.
// - Structs with `Drop`, generic structs other than `Vec<T>`, and recursive structs are unsupported.

use std::cell::{Cell, RefCell};
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
use rustc_span::Span;
use rustc_span::source_map::Spanned;
use z3::ast::{Ast, Bool, Datatype, Dynamic, Int, Seq};
use z3::{
    DatatypeAccessor, DatatypeBuilder, DatatypeSort, FuncDecl, SatResult, Solver, Sort, SortKind,
};

use crate::prepass::{
    AssertionContracts, AssumptionContracts, ContractParam, FunctionContract,
    FunctionContractEntry, LoopContract, LoopContracts, ResolvedExprEnv, SpecVarBinding,
    compute_directives, spec_ty_for_rust_ty, vec_element_ty,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{BinaryOp, BuiltinFn, SpecTy, TypedExpr, TypedExprKind, UnaryOp};

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

#[derive(Debug, Clone, PartialEq, Eq)]
enum SymValue {
    Bool(Bool),
    Int(Int),
    Seq(Seq),
    Datatype(Datatype),
}

#[derive(Debug)]
struct TypeEncoding {
    sort: Sort,
    kind: TypeEncodingKind,
}

#[derive(Debug)]
enum TypeEncodingKind {
    Bool,
    Int,
    Seq,
    Datatype(Rc<DatatypeEncoding>),
}

#[derive(Debug)]
struct DatatypeEncoding {
    sort: DatatypeSort,
    fields: Vec<Rc<TypeEncoding>>,
}

impl DatatypeEncoding {
    fn constructor(&self) -> &z3::FuncDecl {
        &self.sort.variants[0].constructor
    }

    fn accessor(&self, index: usize) -> &z3::FuncDecl {
        &self.sort.variants[0].accessors[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ControlPoint {
    basic_block: BasicBlock,
    statement_index: usize,
}

#[derive(Debug, Clone)]
pub struct State {
    pc: Bool,
    assertion: Bool,
    model: BTreeMap<Local, SymValue>,
    ctrl: ControlPoint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BoolExpr {
    Const(bool),
    Value(SymValue),
    Not(Box<BoolExpr>),
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: Body<'tcx>,
    contracts: HashMap<LocalDefId, FunctionContractEntry>,
    function_spec_vars: HashMap<String, SymValue>,
    loop_contracts: LoopContracts,
    assertion_contracts: AssertionContracts,
    assumption_contracts: AssumptionContracts,
    prepass_error: Option<VerificationResult>,
    next_sym: Cell<usize>,
    type_encodings: RefCell<BTreeMap<SpecTy, Rc<TypeEncoding>>>,
}

impl<'tcx> Verifier<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        item_span: Span,
        body: Body<'tcx>,
        contracts: HashMap<LocalDefId, FunctionContractEntry>,
    ) -> Self {
        let (
            loop_contracts,
            assertion_contracts,
            assumption_contracts,
            function_contract,
            spec_vars,
            prepass_error,
        ) = match compute_directives(tcx, def_id, item_span, &body) {
            Ok(prepass) => (
                prepass.loop_contracts,
                prepass.assertion_contracts,
                prepass.assumption_contracts,
                prepass.function_contract,
                prepass.spec_vars,
                None,
            ),
            Err(error) => (
                LoopContracts::empty(),
                AssertionContracts::empty(),
                AssumptionContracts::empty(),
                None,
                Vec::new(),
                Some(VerificationResult {
                    function: tcx.def_path_str(def_id.to_def_id()),
                    status: VerificationStatus::Unsupported,
                    span: error
                        .display_span
                        .unwrap_or_else(|| span_text(tcx, error.span)),
                    message: error.message,
                }),
            ),
        };
        let next_sym = Cell::new(0);
        let mut contracts = contracts;
        if let Some(contract) = function_contract {
            contracts.insert(def_id, FunctionContractEntry::Ready(contract));
        } else if let Some(error) = prepass_error.clone() {
            contracts.insert(def_id, FunctionContractEntry::Invalid(error));
        }
        let verifier = Self {
            tcx,
            def_id,
            body,
            contracts,
            function_spec_vars: HashMap::new(),
            loop_contracts,
            assertion_contracts,
            assumption_contracts,
            prepass_error,
            next_sym,
            type_encodings: RefCell::new(BTreeMap::new()),
        };
        let function_spec_vars = verifier.instantiate_spec_vars(&spec_vars);
        Self {
            function_spec_vars,
            ..verifier
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
            if let Some(assumption) = self
                .assumption_contracts
                .assumption_at(ctrl.basic_block, ctrl.statement_index)
            {
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
                self.assume_constraint(&mut state, formula);
            }
            match self.check_sat(std::slice::from_ref(&state.pc)) {
                SatResult::Sat => {}
                SatResult::Unsat => continue,
                SatResult::Unknown => {
                    return self.unknown_result(
                        self.control_span(ctrl),
                        "solver returned unknown while checking assumption".to_owned(),
                    );
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
                if let Some(FunctionContractEntry::Ready(contract)) =
                    self.contracts.get(&self.def_id)
                {
                    let formula = self.function_postcondition_to_z3(&state, contract)?;
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
                                not_expr(BoolExpr::Value(discr_value.clone()))
                            } else {
                                BoolExpr::Value(discr_value.clone())
                            }
                        }
                        _ => BoolExpr::Value(self.value_wrap_bool(&self.eq_for_spec_ty(
                            &self.spec_ty_for_place_ty(
                                discr.ty(&self.body.local_decls, self.tcx),
                                term.source_info.span,
                            )?,
                            &discr_value,
                            &self.value_int(value as i64),
                            term.source_info.span,
                        )?)),
                    };
                    let branch = self.bool_expr_to_z3(&branch)?;
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
                let mut formula = BoolExpr::Value(cond_value);
                if !*expected {
                    formula = not_expr(formula);
                }
                let formula = self.bool_expr_to_z3(&formula)?;
                self.require_constraint(
                    &mut state,
                    formula,
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
            let contract = match self.contracts.get(&def_id) {
                Some(FunctionContractEntry::Ready(contract)) => contract,
                Some(FunctionContractEntry::Invalid(error)) => {
                    return Err(self.invalid_local_contract_result(def_id, error));
                }
                None => return Err(self.missing_local_contract_result(def_id, span)),
            };
            let spec = self.instantiate_contract_spec_vars(contract);
            let env = self.call_env(&state, args, contract, span, spec.clone())?;
            let req = self.contract_req_to_z3(contract, &env, span)?;
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
            let mut env = self.call_env(&state, args, contract, span, spec)?;
            self.consume_call_move_args(&mut state, args, span)?;
            env.current.insert("result".to_owned(), result_value);
            let ens = self.contract_ens_to_z3(contract, &env, span)?;
            self.assume_constraint(&mut state, ens);
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
            let invariant = self.spec_expr_to_bool(
                &state,
                &loop_contract.invariant,
                &loop_contract.resolution,
            )?;
            let invariant = self.bool_expr_to_z3(&invariant)?;
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
        match self.check_sat(std::slice::from_ref(&state.pc)) {
            SatResult::Unsat => None,
            SatResult::Sat => {
                let ctrl = state.ctrl;
                let bucket = pending.entry(ctrl).or_default();
                if bucket.is_empty() {
                    worklist.push_back(ctrl);
                }
                bucket.push(state);
                None
            }
            SatResult::Unknown => Some(self.unknown_result(
                self.control_span(state.ctrl),
                "solver returned unknown while checking path feasibility".to_owned(),
            )),
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
        if let Some(FunctionContractEntry::Ready(contract)) = self.contracts.get(&self.def_id) {
            let env =
                CallEnv::for_function(self, &state, contract, self.function_spec_vars.clone())?;
            let req = self.contract_req_to_z3(contract, &env, self.tcx.def_span(self.def_id))?;
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
        let ty = self.body.local_decls[local].ty;
        let formula = self.resolve_formula(ty, value, span)?;
        self.require_constraint(
            state,
            formula,
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
                    let result_ty = self
                        .spec_ty_for_place_ty(rvalue.ty(&self.body.local_decls, self.tcx), span)?;
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
                    let result_ty =
                        spec_ty_for_rust_ty(self.tcx, rvalue.ty(&self.body.local_decls, self.tcx))
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
        let lhs_ty = lhs.ty(&self.body.local_decls, self.tcx);
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
        let result_ty = lhs.ty(&self.body.local_decls, self.tcx);
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
        let operand_ty = operand.ty(&self.body.local_decls, self.tcx);
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
        let root_ty = self.body.local_decls[place.local].ty;
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
        let root_ty = self.body.local_decls[place.local].ty;
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
            SpecTy::Seq(_) => self.fresh_for_spec_ty(spec_ty, "dangle"),
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
            TypedExprKind::BuiltinCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.spec_expr_to_value(state, arg, resolved)?);
                }
                self.eval_builtin_call(*func, args, values, self.control_span(state.ctrl))
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
            TypedExprKind::Int(value) => {
                self.value_decimal_int(&value.digits, self.tcx.def_span(self.def_id))
            }
            TypedExprKind::Var(name) if spec.contains_key(name) => {
                spec.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            TypedExprKind::Var(name) => current.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing contract binding `{name}`"),
                )
            }),
            TypedExprKind::Bind(name) => spec.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing spec binding `{name}`"),
                )
            }),
            TypedExprKind::BuiltinCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.contract_expr_to_value(current, spec, arg)?);
                }
                self.eval_builtin_call(*func, args, values, self.tcx.def_span(self.def_id))
            }
            TypedExprKind::Field { base, index, .. } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                self.project_field(value, &base.ty, *index, self.tcx.def_span(self.def_id))
            }
            TypedExprKind::TupleField { base, index } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                self.project_field(value, &base.ty, *index, self.tcx.def_span(self.def_id))
            }
            TypedExprKind::Deref { base } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                match &base.ty {
                    crate::spec::SpecTy::Ref(inner) => {
                        self.ref_deref(&value, inner, self.tcx.def_span(self.def_id))
                    }
                    crate::spec::SpecTy::Mut(inner) => {
                        self.mut_cur(&value, inner, self.tcx.def_span(self.def_id))
                    }
                    _ => unreachable!("typed deref base"),
                }
            }
            TypedExprKind::Fin { base } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                let SpecTy::Mut(inner) = &base.ty else {
                    unreachable!("typed fin base");
                };
                self.mut_fin(&value, inner, self.tcx.def_span(self.def_id))
            }
            TypedExprKind::Unary { op, arg } => {
                let value = self.contract_expr_to_value(current, spec, arg)?;
                Ok(self.lower_unary_value(*op, &value))
            }
            TypedExprKind::Binary { op, lhs, rhs } => {
                let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                self.lower_binary_value(
                    *op,
                    &lhs.ty,
                    &lhs_value,
                    &rhs_value,
                    self.tcx.def_span(self.def_id),
                )
            }
        }
    }

    fn eval_builtin_call(
        &self,
        func: BuiltinFn,
        args: &[TypedExpr],
        values: Vec<SymValue>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match func {
            BuiltinFn::SeqLen => {
                let SymValue::Seq(seq) = &values[0] else {
                    return Err(self.unsupported_result(span, "expected sequence value".to_owned()));
                };
                Ok(self.value_wrap_int(&seq.length()))
            }
            BuiltinFn::SeqExtract => {
                let SymValue::Seq(seq) = &values[0] else {
                    return Err(self.unsupported_result(span, "expected sequence value".to_owned()));
                };
                let SpecTy::Seq(inner) = &args[0].ty else {
                    unreachable!("typed seq_extract base");
                };
                let start = self.value_int_data(&values[1]);
                let len = self.value_int_data(&values[2]);
                Ok(SymValue::Seq(self.seq_extract(seq, inner, &start, &len)))
            }
            BuiltinFn::SeqConcat => {
                let (SymValue::Seq(lhs), SymValue::Seq(rhs)) = (&values[0], &values[1]) else {
                    return Err(self.unsupported_result(
                        span,
                        "expected sequence values for concatenation".to_owned(),
                    ));
                };
                Ok(SymValue::Seq(Seq::concat(&[lhs, rhs])))
            }
            BuiltinFn::SeqNth => {
                let SymValue::Seq(seq) = &values[0] else {
                    return Err(self.unsupported_result(span, "expected sequence value".to_owned()));
                };
                let SpecTy::Seq(inner) = &args[0].ty else {
                    unreachable!("typed seq_nth base");
                };
                let index = self.value_int_data(&values[1]);
                let dyn_value = seq.nth(index);
                let encoding = self.type_encoding(inner)?;
                let elem = self.decode_value(&encoding, dyn_value, span)?;
                Ok(elem)
            }
            BuiltinFn::SeqRev => {
                let SymValue::Seq(seq) = &values[0] else {
                    return Err(self.unsupported_result(span, "expected sequence value".to_owned()));
                };
                let SpecTy::Seq(inner) = &args[0].ty else {
                    unreachable!("typed seq_rev base");
                };
                Ok(SymValue::Seq(self.seq_rev(seq, inner)))
            }
            BuiltinFn::SeqUnit => Ok(SymValue::Seq(match &values[0] {
                SymValue::Bool(value) => Seq::unit(value),
                SymValue::Int(value) => Seq::unit(value),
                SymValue::Seq(value) => Seq::unit(value),
                SymValue::Datatype(value) => Seq::unit(value),
            })),
        }
    }

    fn seq_extract(&self, seq: &Seq, inner: &SpecTy, start: &Int, len: &Int) -> Seq {
        let elem = self
            .type_encoding(inner)
            .expect("sequence element encoding for seq_extract");
        let seq_sort = Sort::seq(&elem.sort);
        let decl = FuncDecl::new(
            format!("seq_extract_{}", self.sort_name(inner)),
            &[&seq_sort, &Sort::int(), &Sort::int()],
            &seq_sort,
        );
        let input = Seq::fresh_const("seq_extract_input", &elem.sort);
        let start_var = Int::fresh_const("seq_extract_start");
        let len_var = Int::fresh_const("seq_extract_len");
        let output = decl
            .apply(&[&input, &start_var, &len_var])
            .as_seq()
            .expect("seq_extract result");
        let idx = Int::fresh_const("seq_extract_idx");
        let input_len = input.length();
        let in_bounds = bool_and(vec![
            start_var.ge(0),
            len_var.ge(0),
            start_var.le(input_len.clone()),
            len_var.le(input_len.clone() - start_var.clone()),
        ]);
        GLOBAL_SOLVER.with(|solver| {
            solver.assert(&z3::ast::forall_const(
                &[&input, &start_var, &len_var],
                &[],
                &in_bounds.clone().implies(output.length().eq(&len_var)),
            ));
            solver.assert(&z3::ast::forall_const(
                &[&input, &start_var, &len_var, &idx],
                &[],
                &bool_and(vec![in_bounds.clone(), idx.ge(0), idx.lt(len_var.clone())]).implies(
                    output
                        .nth(idx.clone())
                        .eq(input.nth(start_var.clone() + idx.clone())),
                ),
            ));
            let zero = Int::from_i64(0);
            let prefix = decl
                .apply(&[&input, &zero, &start_var])
                .as_seq()
                .expect("seq_extract prefix");
            let suffix_start = start_var.clone() + len_var.clone();
            let suffix_len = input_len.clone() - start_var.clone() - len_var.clone();
            let suffix = decl
                .apply(&[&input, &suffix_start, &suffix_len])
                .as_seq()
                .expect("seq_extract suffix");
            solver.assert(&z3::ast::forall_const(
                &[&input, &start_var, &len_var],
                &[],
                &in_bounds.implies(input.eq(Seq::concat(&[&prefix, &output, &suffix]))),
            ));
        });
        decl.apply(&[seq, start, len])
            .as_seq()
            .expect("seq_extract application")
    }

    fn seq_rev(&self, seq: &Seq, inner: &SpecTy) -> Seq {
        let elem = self
            .type_encoding(inner)
            .expect("sequence element encoding for seq_rev");
        let seq_sort = Sort::seq(&elem.sort);
        let decl = FuncDecl::new(
            format!("seq_rev_{}", self.sort_name(inner)),
            &[&seq_sort],
            &seq_sort,
        );
        let input = Seq::fresh_const("seq_rev_input", &elem.sort);
        let output = decl.apply(&[&input]).as_seq().expect("seq_rev result");
        let index = Int::fresh_const("seq_rev_idx");
        let len = input.length();
        GLOBAL_SOLVER.with(|solver| {
            solver.assert(&z3::ast::forall_const(
                &[&input],
                &[],
                &output.length().eq(&len),
            ));
            solver.assert(&z3::ast::forall_const(
                &[&input, &index],
                &[],
                &bool_and(vec![
                    index.ge(0),
                    index.lt(len.clone()),
                    output
                        .nth(index.clone())
                        .eq(input.nth(len.clone() - index.clone() - 1)),
                ]),
            ));
            let left = Seq::fresh_const("seq_rev_left", &elem.sort);
            let right = Seq::fresh_const("seq_rev_right", &elem.sort);
            let left_rev = decl.apply(&[&left]).as_seq().expect("seq_rev left");
            let right_rev = decl.apply(&[&right]).as_seq().expect("seq_rev right");
            let both = Seq::concat(&[&left, &right]);
            solver.assert(&z3::ast::forall_const(
                &[&left, &right],
                &[],
                &decl
                    .apply(&[&both])
                    .as_seq()
                    .expect("seq_rev concat")
                    .eq(Seq::concat(&[&right_rev, &left_rev])),
            ));
        });
        decl.apply(&[seq]).as_seq().expect("seq_rev application")
    }

    fn function_postcondition_to_z3(
        &self,
        state: &State,
        contract: &FunctionContract,
    ) -> Result<Bool, VerificationResult> {
        let env = CallEnv::for_function(self, state, contract, self.function_spec_vars.clone())?;
        self.contract_ens_to_z3(contract, &env, self.tcx.def_span(self.def_id))
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
        match self.check_sat(&[state.pc.clone(), state.assertion.clone()]) {
            SatResult::Sat => Ok(()),
            SatResult::Unsat => Err(VerificationResult {
                function: self.tcx.def_path_str(self.def_id.to_def_id()),
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

    fn assume_constraint(&self, state: &mut State, constraint: Bool) {
        state.pc = bool_and(vec![state.pc.clone(), constraint]);
    }

    fn assert_constraint(&self, state: &mut State, constraint: Bool) {
        state.assertion = bool_and(vec![state.assertion.clone(), constraint]);
    }

    fn check_sat(&self, assumptions: &[Bool]) -> SatResult {
        with_solver(|solver| solver.check_assumptions(assumptions))
    }

    fn bool_expr_to_z3(&self, expr: &BoolExpr) -> Result<Bool, VerificationResult> {
        match expr {
            BoolExpr::Const(value) => Ok(Bool::from_bool(*value)),
            BoolExpr::Value(value) => Ok(self.value_is_true(value)),
            BoolExpr::Not(arg) => Ok(self.bool_expr_to_z3(arg)?.not()),
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
        let inner_spec_ty = self.spec_ty_for_place_ty(inner_ty, self.tcx.def_span(self.def_id))?;
        let final_value = self.mut_fin(value, &inner_spec_ty, self.tcx.def_span(self.def_id))?;
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

    fn is_immediate_return_block(&self, block: BasicBlock) -> bool {
        let data = &self.body.basic_blocks[block];
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

    fn invalid_local_contract_result(
        &self,
        def_id: LocalDefId,
        err: &VerificationResult,
    ) -> VerificationResult {
        let callee = self.tcx.def_path_str(def_id.to_def_id());
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: err.status.clone(),
            span: err.span.clone(),
            message: format!("callee `{callee}` has invalid contract: {}", err.message),
        }
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

    fn value_int(&self, value: i64) -> SymValue {
        SymValue::Int(Int::from_i64(value))
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
        SymValue::Bool(value.clone())
    }

    fn value_wrap_int(&self, value: &Int) -> SymValue {
        SymValue::Int(value.clone())
    }

    fn value_is_true(&self, value: &SymValue) -> Bool {
        match value {
            SymValue::Bool(value) => value.clone(),
            _ => unreachable!("typed bool expression lowered to non-bool value"),
        }
    }

    fn value_int_data(&self, value: &SymValue) -> Int {
        match value {
            SymValue::Int(value) => value.clone(),
            _ => unreachable!("typed int expression lowered to non-int value"),
        }
    }

    fn value_bool_data(&self, value: &SymValue) -> Bool {
        match value {
            SymValue::Bool(value) => value.clone(),
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
            TypeEncodingKind::Bool => Ok(self.value_bool_data(lhs).eq(self.value_bool_data(rhs))),
            TypeEncodingKind::Int => Ok(self.value_int_data(lhs).eq(self.value_int_data(rhs))),
            TypeEncodingKind::Seq => {
                let (SymValue::Seq(lhs), SymValue::Seq(rhs)) = (lhs, rhs) else {
                    return Err(self.unsupported_result(
                        span,
                        "expected sequence values for equality".to_owned(),
                    ));
                };
                Ok(lhs.eq(rhs))
            }
            TypeEncodingKind::Datatype(_) => {
                let (SymValue::Datatype(lhs), SymValue::Datatype(rhs)) = (lhs, rhs) else {
                    return Err(self.unsupported_result(
                        span,
                        "expected datatype values for equality".to_owned(),
                    ));
                };
                Ok(lhs.eq(rhs))
            }
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
        if let Some(encoding) = self.type_encodings.borrow().get(ty).cloned() {
            return Ok(encoding);
        }
        let encoding = self.build_type_encoding(ty)?;
        self.type_encodings
            .borrow_mut()
            .insert(ty.clone(), encoding.clone());
        Ok(encoding)
    }

    fn datatype_encoding(&self, ty: &SpecTy) -> Result<Rc<DatatypeEncoding>, VerificationResult> {
        let encoding = self.type_encoding(ty)?;
        match &encoding.kind {
            TypeEncodingKind::Datatype(encoding) => Ok(encoding.clone()),
            _ => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                format!("expected datatype-backed spec type, found {ty:?}"),
            )),
        }
    }

    fn build_type_encoding(&self, ty: &SpecTy) -> Result<Rc<TypeEncoding>, VerificationResult> {
        let encoding = match ty {
            SpecTy::Bool => TypeEncoding {
                sort: Sort::bool(),
                kind: TypeEncodingKind::Bool,
            },
            SpecTy::IntLiteral
            | SpecTy::I8
            | SpecTy::I16
            | SpecTy::I32
            | SpecTy::I64
            | SpecTy::Isize
            | SpecTy::U8
            | SpecTy::U16
            | SpecTy::U32
            | SpecTy::U64
            | SpecTy::Usize => TypeEncoding {
                sort: Sort::int(),
                kind: TypeEncodingKind::Int,
            },
            SpecTy::Seq(inner) => {
                let elem = self.type_encoding(inner)?;
                TypeEncoding {
                    sort: Sort::seq(&elem.sort),
                    kind: TypeEncodingKind::Seq,
                }
            }
            SpecTy::Tuple(_) | SpecTy::Struct(_) | SpecTy::Ref(_) | SpecTy::Mut(_) => {
                let datatype = self.build_datatype_encoding(ty)?;
                TypeEncoding {
                    sort: datatype.sort.sort.clone(),
                    kind: TypeEncodingKind::Datatype(datatype),
                }
            }
        };
        Ok(Rc::new(encoding))
    }

    fn build_datatype_encoding(
        &self,
        ty: &SpecTy,
    ) -> Result<Rc<DatatypeEncoding>, VerificationResult> {
        let field_names = self.datatype_field_names(ty)?;
        let field_encodings = self.datatype_field_encodings(ty)?;
        let fields = field_names
            .iter()
            .zip(field_encodings.iter())
            .map(|(name, encoding)| (name.as_str(), DatatypeAccessor::Sort(encoding.sort.clone())))
            .collect::<Vec<_>>();
        Ok(Rc::new(DatatypeEncoding {
            sort: DatatypeBuilder::new(self.sort_name(ty))
                .variant("mk", fields)
                .finish(),
            fields: field_encodings,
        }))
    }

    fn datatype_field_names(&self, ty: &SpecTy) -> Result<Vec<String>, VerificationResult> {
        match ty {
            SpecTy::Ref(_) => Ok(vec!["deref".to_owned()]),
            SpecTy::Mut(_) => Ok(vec!["cur".to_owned(), "fin".to_owned()]),
            SpecTy::Tuple(items) => Ok((0..items.len()).map(|index| format!("_{index}")).collect()),
            SpecTy::Struct(struct_ty) => Ok(struct_ty
                .fields
                .iter()
                .map(|field| field.name.clone())
                .collect()),
            other => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                format!("expected datatype-backed spec type, found {other:?}"),
            )),
        }
    }

    fn datatype_field_encodings(
        &self,
        ty: &SpecTy,
    ) -> Result<Vec<Rc<TypeEncoding>>, VerificationResult> {
        match ty {
            SpecTy::Ref(inner) => Ok(vec![self.type_encoding(inner)?]),
            SpecTy::Mut(inner) => {
                let inner = self.type_encoding(inner)?;
                Ok(vec![inner.clone(), inner])
            }
            SpecTy::Tuple(items) => items.iter().map(|item| self.type_encoding(item)).collect(),
            SpecTy::Struct(struct_ty) => struct_ty
                .fields
                .iter()
                .map(|field| self.type_encoding(&field.ty))
                .collect(),
            other => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                format!("expected datatype-backed spec type, found {other:?}"),
            )),
        }
    }

    fn sort_name(&self, ty: &SpecTy) -> String {
        fn sanitize(raw: &str) -> String {
            raw.chars()
                .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
                .collect()
        }
        match ty {
            SpecTy::Bool => "bool".to_owned(),
            SpecTy::IntLiteral => "int_lit".to_owned(),
            SpecTy::I8 => "i8".to_owned(),
            SpecTy::I16 => "i16".to_owned(),
            SpecTy::I32 => "i32".to_owned(),
            SpecTy::I64 => "i64".to_owned(),
            SpecTy::Isize => "isize".to_owned(),
            SpecTy::U8 => "u8".to_owned(),
            SpecTy::U16 => "u16".to_owned(),
            SpecTy::U32 => "u32".to_owned(),
            SpecTy::U64 => "u64".to_owned(),
            SpecTy::Usize => "usize".to_owned(),
            SpecTy::Seq(inner) => format!("seq_{}", self.sort_name(inner)),
            SpecTy::Tuple(items) => format!(
                "tuple_{}",
                items
                    .iter()
                    .map(|item| self.sort_name(item))
                    .collect::<Vec<_>>()
                    .join("_")
            ),
            SpecTy::Struct(struct_ty) => format!("struct_{}", sanitize(&struct_ty.name)),
            SpecTy::Ref(inner) => format!("ref_{}", self.sort_name(inner)),
            SpecTy::Mut(inner) => format!("mut_{}", self.sort_name(inner)),
        }
    }

    fn sort_for_spec_ty(&self, ty: &SpecTy) -> Result<Sort, VerificationResult> {
        Ok(self.type_encoding(ty)?.sort.clone())
    }

    fn construct_datatype(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.datatype_encoding(ty)?;
        let asts = fields.iter().map(sym_value_ast).collect::<Vec<_>>();
        Ok(SymValue::Datatype(
            encoding.constructor().apply(&asts).as_datatype().unwrap(),
        ))
    }

    fn decode_value(
        &self,
        encoding: &TypeEncoding,
        value: Dynamic,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match &encoding.kind {
            TypeEncodingKind::Bool => value
                .as_bool()
                .map(SymValue::Bool)
                .ok_or_else(|| self.unsupported_result(span, "expected bool Z3 value".to_owned())),
            TypeEncodingKind::Int => value
                .as_int()
                .map(SymValue::Int)
                .ok_or_else(|| self.unsupported_result(span, "expected int Z3 value".to_owned())),
            TypeEncodingKind::Seq => value.as_seq().map(SymValue::Seq).ok_or_else(|| {
                self.unsupported_result(span, "expected sequence Z3 value".to_owned())
            }),
            TypeEncodingKind::Datatype(_) => {
                value.as_datatype().map(SymValue::Datatype).ok_or_else(|| {
                    self.unsupported_result(span, "expected datatype Z3 value".to_owned())
                })
            }
        }
    }

    fn fresh_for_rust_ty(&self, ty: Ty<'tcx>, hint: &str) -> Result<SymValue, VerificationResult> {
        if let TyKind::Adt(adt_def, args) = ty.kind()
            && vec_element_ty(self.tcx, ty).is_none()
        {
            if !adt_def.is_struct() {
                return Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("unsupported type {ty:?}"),
                ));
            }
            if !args.is_empty() {
                return Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("generic structs are unsupported: {ty:?}"),
                ));
            }
            if adt_def.has_dtor(self.tcx) {
                return Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("structs with Drop are unsupported: {ty:?}"),
                ));
            }
        }
        let spec_ty = spec_ty_for_rust_ty(self.tcx, ty)
            .map_err(|err| self.unsupported_result(self.tcx.def_span(self.def_id), err))?;
        self.fresh_for_spec_ty(&spec_ty, hint)
    }

    fn fresh_for_spec_ty(&self, ty: &SpecTy, hint: &str) -> Result<SymValue, VerificationResult> {
        match ty {
            SpecTy::Bool => Ok(self.value_wrap_bool(&Bool::new_const(self.fresh_name(hint)))),
            SpecTy::IntLiteral
            | SpecTy::I8
            | SpecTy::I16
            | SpecTy::I32
            | SpecTy::I64
            | SpecTy::Isize
            | SpecTy::U8
            | SpecTy::U16
            | SpecTy::U32
            | SpecTy::U64
            | SpecTy::Usize => Ok(self.value_wrap_int(&Int::new_const(self.fresh_name(hint)))),
            SpecTy::Seq(inner) => Ok(SymValue::Seq(Seq::new_const(
                self.fresh_name(hint),
                &self.sort_for_spec_ty(inner)?,
            ))),
            SpecTy::Tuple(items) => {
                let mut values = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    values.push(self.fresh_for_spec_ty(item, &format!("{hint}_{index}"))?);
                }
                self.construct_datatype(ty, &values)
            }
            SpecTy::Struct(struct_ty) => {
                let mut values = Vec::with_capacity(struct_ty.fields.len());
                for field in &struct_ty.fields {
                    values.push(
                        self.fresh_for_spec_ty(&field.ty, &format!("{hint}_{}", field.name))?,
                    );
                }
                self.construct_datatype(ty, &values)
            }
            SpecTy::Ref(inner) => {
                let deref_value = self.fresh_for_spec_ty(inner, &format!("{hint}_deref"))?;
                self.construct_datatype(ty, &[deref_value])
            }
            SpecTy::Mut(inner) => {
                let cur = self.fresh_for_spec_ty(inner, &format!("{hint}_cur"))?;
                let fin = self.fresh_for_spec_ty(inner, &format!("{hint}_fin"))?;
                self.construct_datatype(ty, &[cur, fin])
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
        let SymValue::Datatype(value) = value else {
            return Err(self.unsupported_result(
                span,
                "field projection requires datatype-backed value".to_owned(),
            ));
        };
        let encoding = self.datatype_encoding(parent_ty)?;
        let field = encoding
            .fields
            .get(index)
            .ok_or_else(|| self.unsupported_result(span, "field index out of range".to_owned()))?;
        self.decode_value(field, encoding.accessor(index).apply(&[&value]), span)
    }

    fn ref_deref(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let SymValue::Datatype(value) = value else {
            return Err(self.unsupported_result(span, "expected shared reference value".to_owned()));
        };
        let encoding = self.datatype_encoding(&SpecTy::Ref(Box::new(inner_ty.clone())))?;
        self.decode_value(
            &encoding.fields[0],
            encoding.accessor(0).apply(&[value]),
            span,
        )
    }

    fn mut_cur(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let SymValue::Datatype(value) = value else {
            return Err(
                self.unsupported_result(span, "expected mutable reference value".to_owned())
            );
        };
        let encoding = self.datatype_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_value(
            &encoding.fields[0],
            encoding.accessor(0).apply(&[value]),
            span,
        )
    }

    fn mut_fin(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let SymValue::Datatype(value) = value else {
            return Err(
                self.unsupported_result(span, "expected mutable reference value".to_owned())
            );
        };
        let encoding = self.datatype_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_value(
            &encoding.fields[1],
            encoding.accessor(1).apply(&[value]),
            span,
        )
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
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "invalid isize lower bound".to_owned(),
                )
            })?;
            let upper = Int::from_str(&upper.to_string()).map_err(|()| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "invalid isize upper bound".to_owned(),
                )
            })?;
            Ok((lower, upper))
        } else {
            let upper = (1_u128 << bits) - 1;
            let upper = Int::from_str(&upper.to_string()).map_err(|()| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "invalid usize upper bound".to_owned(),
                )
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
        match ty {
            SpecTy::Bool | SpecTy::IntLiteral => Ok(None),
            SpecTy::I8
            | SpecTy::I16
            | SpecTy::I32
            | SpecTy::I64
            | SpecTy::Isize
            | SpecTy::U8
            | SpecTy::U16
            | SpecTy::U32
            | SpecTy::U64
            | SpecTy::Usize => self.int_range_formula_for_spec_ty(ty, value, span),
            SpecTy::Ref(inner) => {
                let deref_value = self.ref_deref(value, inner, span)?;
                self.spec_ty_formula(inner, &deref_value, span)
            }
            SpecTy::Mut(inner) => {
                let current = self.mut_cur(value, inner, span)?;
                self.spec_ty_formula(inner, &current, span)
            }
            SpecTy::Seq(item) => Ok(Some(self.list_type_invariant(item, value, span)?)),
            SpecTy::Tuple(items) => {
                let mut formulas = Vec::new();
                for (index, item) in items.iter().enumerate() {
                    let field = self.project_field(value.clone(), ty, index, span)?;
                    if let Some(formula) = self.spec_ty_formula(item, &field, span)? {
                        formulas.push(formula);
                    }
                }
                if formulas.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(bool_and(formulas)))
                }
            }
            SpecTy::Struct(struct_ty) => {
                let mut formulas = Vec::new();
                for (index, field_ty) in struct_ty.fields.iter().enumerate() {
                    let field = self.project_field(value.clone(), ty, index, span)?;
                    if let Some(formula) = self.spec_ty_formula(&field_ty.ty, &field, span)? {
                        formulas.push(formula);
                    }
                }
                if formulas.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(bool_and(formulas)))
                }
            }
        }
    }

    fn resolve_formula_for_spec_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match ty {
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
            | SpecTy::Usize => Ok(Bool::from_bool(true)),
            SpecTy::Ref(_) => Ok(Bool::from_bool(true)),
            SpecTy::Mut(inner) => {
                let cur = self.mut_cur(value, inner, span)?;
                let fin = self.mut_fin(value, inner, span)?;
                self.eq_for_spec_ty(inner, &cur, &fin, span)
            }
            SpecTy::Seq(item) => self.list_resolve_formula(item, value, span),
            SpecTy::Tuple(items) => {
                let mut formulas = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    let field = self.project_field(value.clone(), ty, index, span)?;
                    formulas.push(self.resolve_formula_for_spec_ty(item, &field, span)?);
                }
                Ok(bool_and(formulas))
            }
            SpecTy::Struct(struct_ty) => {
                let mut formulas = Vec::with_capacity(struct_ty.fields.len());
                for (index, field_ty) in struct_ty.fields.iter().enumerate() {
                    let field = self.project_field(value.clone(), ty, index, span)?;
                    formulas.push(self.resolve_formula_for_spec_ty(&field_ty.ty, &field, span)?);
                }
                Ok(bool_and(formulas))
            }
        }
    }

    fn list_resolve_formula(
        &self,
        item: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let SymValue::Seq(seq) = value else {
            return Err(self.unsupported_result(span, "expected sequence value".to_owned()));
        };
        let index = Int::new_const(self.fresh_name("resolve_idx"));
        let elem_encoding = self.type_encoding(item)?;
        let elem = self.decode_value(&elem_encoding, seq.nth(index.clone()), span)?;
        let body = bool_and(vec![index.ge(0), index.lt(seq.length())])
            .implies(self.resolve_formula_for_spec_ty(item, &elem, span)?);
        Ok(z3::ast::forall_const(&[&index], &[], &body))
    }

    fn list_type_invariant(
        &self,
        item: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let SymValue::Seq(seq) = value else {
            return Err(self.unsupported_result(span, "expected sequence value".to_owned()));
        };
        let index = Int::new_const(self.fresh_name("list_inv_idx"));
        let elem_encoding = self.type_encoding(item)?;
        let elem = self.decode_value(&elem_encoding, seq.nth(index.clone()), span)?;
        let elem_inv = self
            .spec_ty_formula(item, &elem, span)?
            .unwrap_or_else(|| Bool::from_bool(true));
        let body = bool_and(vec![index.ge(0), index.lt(seq.length())]).implies(elem_inv);
        Ok(z3::ast::forall_const(&[&index], &[], &body))
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
        self.require_constraint(state, formula, span, span_text(self.tcx, span), message)
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
        self.require_constraint(
            state,
            bool_and(vec![value.ge(lower), value.le(upper)]),
            span,
            span_text(self.tcx, span),
            message,
        )
    }

    fn unsupported_result(&self, span: Span, message: String) -> VerificationResult {
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: VerificationStatus::Unsupported,
            span: span_text(self.tcx, span),
            message,
        }
    }

    fn unknown_result(&self, span: Span, message: String) -> VerificationResult {
        VerificationResult {
            function: self.tcx.def_path_str(self.def_id.to_def_id()),
            status: VerificationStatus::Unknown,
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
            .zip(verifier.body.local_decls.indices().skip(1))
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
        SpecTy::Seq(inner) | SpecTy::Ref(inner) => spec_ty_contains_mut_ref(inner),
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

fn sym_value_ast(value: &SymValue) -> &dyn Ast {
    match value {
        SymValue::Bool(value) => value,
        SymValue::Int(value) => value,
        SymValue::Seq(value) => value,
        SymValue::Datatype(value) => value,
    }
}
