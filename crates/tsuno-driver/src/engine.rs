#![allow(clippy::result_large_err)]

// Supported Rust types are reflected into the spec language and encoded in Z3 as follows:
//
// | Rust type                          | spec type           | Z3 representation           | invariant |
// | ---------------------------------- | ------------------- | --------------------------- | --------- |
// | `bool`                             | `bool`              | boxed value                 | `true` |
// | `i8`, `i16`, `i32`, `i64`, `isize` | same as Rust        | boxed value                 | width bounds |
// | `u8`, `u16`, `u32`, `u64`, `usize` | same as Rust        | boxed value                 | width bounds |
// | raw pointers                       | `Ptr`               | constructor over values     | pointer tag |
// | `&T`                               | `Ref<T>`            | constructor over values     | `inv<T>(deref(x))` |
// | `&mut T`                           | `Mut<T>`            | constructor over values     | `inv<T>(cur(x))` |
// | `(T0, .., Tn)`                     | `Tuple([T0, .., Tn])` | constructor over values   | conjunction of field invariants |
// | `struct S { f0: T0, .., fn: Tn }`  | `S`                 | constructor over values     | conjunction of field invariants |
//
// Notes:
// - `Mut<T>` additionally requires `cur(x) == fin(x)` when the mutable reference is closed.
// - `Ref<T>` and `Mut<T>` carry a `ptr: Ptr` field whose provenance must be
//   present. Raw `Ptr` values may still have no provenance.
// - Structs with `Drop`, generic structs, and recursive structs are unsupported.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::Once;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{
    AggregateKind, BasicBlock, BinOp, Body, BorrowKind, ConstOperand, Local, MutBorrowKind,
    Operand, Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::ty::layout::TyAndLayout;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::source_map::Spanned;
use rustc_span::{DUMMY_SP, Span};
use z3::ast::{Ast, Bool, Dynamic, Int, Seq as Z3Seq};
use z3::{Config, Context, RecFuncDecl, SatResult, Solver, Sort, SortKind};

use crate::prepass::{
    ContractParam, ControlPointDirective, ControlPointDirectives, DirectivePrepass,
    FunctionContract, LemmaCallContract, LoopContract, LoopContracts, NormalizedBinding,
    NormalizedPredicate, ProgramPrepass, ResolvedExprEnv, TypedGhostMatchArm, TypedGhostStmt,
    TypedLemmaDef, TypedPureFnDef, spec_ty_for_rust_ty,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{
    BinaryOp, RustTyKey, SpecTy, TypedExpr, TypedExprKind, TypedMatchBinding, UnaryOp,
    option_spec_ty, provenance_spec_ty, ptr_spec_ty,
};
use crate::value::{CompositeEncoding, SymValue, TypeEncoding, TypeEncodingKind, ValueEncoder};

const SOLVER_TIMEOUT_MS: u32 = 1_000;
const GHOST_LOAD_TIMEOUT: Duration = Duration::from_millis(1_000);

thread_local! {
    static GLOBAL_SOLVER: RefCell<Solver> = RefCell::new(build_solver());
}

static Z3_INIT: Once = Once::new();

#[derive(Clone, Copy)]
struct UnsafeCallbackArg<T>(T);

unsafe impl<T> Send for UnsafeCallbackArg<T> {}
unsafe impl<T> Sync for UnsafeCallbackArg<T> {}

impl<T: Copy> UnsafeCallbackArg<T> {
    fn get(self) -> T {
        self.0
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
    model: BTreeMap<Local, SymValue>,
    allocs: BTreeMap<Local, Allocation>,
    spec_env: HashMap<String, SymValue>,
    ctrl: ControlPoint,
}

#[derive(Debug, Clone)]
struct Allocation {
    base_addr: SymValue,
    size: u64,
    align: u64,
}

struct BuiltinNatDecls {
    nat_to_int: RecFuncDecl,
    int_to_nat: RecFuncDecl,
}

struct FunctionContext<'tcx> {
    def_id: LocalDefId,
    body: Body<'tcx>,
    contract: FunctionContract,
    loop_contracts: LoopContracts,
    control_point_directives: ControlPointDirectives,
    unsafe_blocks: Vec<Span>,
}

enum VerifierContext<'tcx> {
    Ghost,
    Function(FunctionContext<'tcx>),
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    context: VerifierContext<'tcx>,
    contracts: HashMap<LocalDefId, FunctionContract>,
    pure_fns: HashMap<String, TypedPureFnDef>,
    pure_fn_decls: HashMap<String, RecFuncDecl>,
    lemmas: HashMap<String, TypedLemmaDef>,
    builtin_nat_decls: RefCell<Option<Rc<BuiltinNatDecls>>>,
    next_sym: Cell<usize>,
    value_encoder: ValueEncoder,
}

#[derive(Debug, Clone)]
struct UnsafeState {
    pc: Bool,
    store: BTreeMap<Local, SymValue>,
    allocs: BTreeMap<Local, Allocation>,
    heap: Vec<Resource>,
    ctrl: ControlPoint,
}

#[derive(Debug, Clone)]
enum Resource {
    PointsTo {
        addr: SymValue,
        ty: SymValue,
        value: Option<SymValue>,
    },
    Alloc {
        base: SymValue,
        size: u64,
        alignment: u64,
    },
}

#[derive(Debug, Clone, Default)]
struct UnsafeBridge {
    locals: BTreeSet<Local>,
}

pub fn verify<'tcx>(tcx: TyCtxt<'tcx>, program: ProgramPrepass) -> Vec<VerificationResult> {
    let ProgramPrepass {
        ghosts,
        functions,
        contracts,
    } = program;
    let tcx_capture = UnsafeCallbackArg(tcx);
    let ghosts_capture = UnsafeCallbackArg(&ghosts);
    let prepass_error = z3::with_z3_config(&Config::new(), move || {
        let tcx = tcx_capture.get();
        let ghosts = ghosts_capture.get();
        let mut verifier = Verifier::new(tcx, HashMap::new());
        for enum_def in ghosts.enums.values() {
            verifier.value_encoder.register_enum_def(enum_def.clone());
        }
        for pure_fn in &ghosts.typed_pure_fns {
            if let Err(error) = verifier.load_ghost_function(pure_fn) {
                return Some(VerificationResult {
                    function: "prepass".to_owned(),
                    ..error
                });
            }
        }
        for lemma in &ghosts.typed_lemmas {
            if let Err(error) = verifier.load_ghost_lemma(lemma) {
                return Some(VerificationResult {
                    function: "prepass".to_owned(),
                    ..error
                });
            }
        }
        None
    });
    if let Some(error) = prepass_error {
        return vec![error];
    }

    let mut results = Vec::new();
    let contracts_capture = UnsafeCallbackArg(&contracts);
    for function in functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function.def_id)
            .steal();
        let needed_pure_fns = collect_needed_pure_fns(
            &function.prepass,
            &ghosts.typed_lemmas,
            &ghosts.typed_pure_fns,
        );
        let def_id = function.def_id;
        let prepass = function.prepass;
        let result = z3::with_z3_config(&Config::new(), move || {
            let tcx = tcx_capture.get();
            let ghosts = ghosts_capture.get();
            let contracts = contracts_capture.get().clone();
            let mut verifier = Verifier::new(tcx, contracts);
            for enum_def in ghosts.enums.values() {
                verifier.value_encoder.register_enum_def(enum_def.clone());
            }
            for pure_fn in &needed_pure_fns {
                if let Err(error) = verifier.load_ghost_function(pure_fn) {
                    return VerificationResult {
                        function: "prepass".to_owned(),
                        ..error
                    };
                }
            }
            for lemma in &ghosts.typed_lemmas {
                verifier.lemmas.insert(lemma.name.clone(), lemma.clone());
            }
            verifier.verify_function(def_id, body, prepass)
        });
        results.push(result);
    }
    results
}

impl<'tcx> Verifier<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, contracts: HashMap<LocalDefId, FunctionContract>) -> Self {
        rebuild_solver();
        Self {
            tcx,
            context: VerifierContext::Ghost,
            contracts,
            pure_fns: HashMap::new(),
            pure_fn_decls: HashMap::new(),
            lemmas: HashMap::new(),
            builtin_nat_decls: RefCell::new(None),
            next_sym: Cell::new(0),
            value_encoder: ValueEncoder::new(tcx.data_layout.pointer_size().bits()),
        }
    }

    fn function_context(&self) -> &FunctionContext<'tcx> {
        match &self.context {
            VerifierContext::Function(context) => context,
            VerifierContext::Ghost => panic!("function verifier context is unavailable"),
        }
    }

    fn body(&self) -> &Body<'tcx> {
        &self.function_context().body
    }

    fn current_contract(&self) -> &FunctionContract {
        &self.function_context().contract
    }

    fn loop_contracts(&self) -> &LoopContracts {
        &self.function_context().loop_contracts
    }

    fn control_point_directives(&self) -> &ControlPointDirectives {
        &self.function_context().control_point_directives
    }

    fn report_span(&self) -> Span {
        match &self.context {
            VerifierContext::Ghost => DUMMY_SP,
            VerifierContext::Function(context) => self.tcx.def_span(context.def_id),
        }
    }

    fn report_function(&self) -> String {
        match &self.context {
            VerifierContext::Ghost => "prepass".to_owned(),
            VerifierContext::Function(context) => self.tcx.def_path_str(context.def_id.to_def_id()),
        }
    }

    fn reset_solver_state(&self) {
        reset_solver();
        self.value_encoder.reset_solver_state();
    }

    pub fn load_ghost_function(
        &mut self,
        pure_fn: &TypedPureFnDef,
    ) -> Result<(), VerificationResult> {
        let load_context = format!("loading pure function `{}`", pure_fn.name);
        let inserted = self
            .pure_fns
            .insert(pure_fn.name.clone(), pure_fn.clone())
            .is_none();
        assert!(inserted, "duplicate pure function `{}`", pure_fn.name);
        let (result, timed_out) =
            with_z3_deadline(GHOST_LOAD_TIMEOUT, || self.register_pure_fn(pure_fn));
        if timed_out {
            return Err(self.timeout_solver_result(self.report_span(), &load_context));
        }
        result
    }

    pub fn load_ghost_lemma(&mut self, lemma: &TypedLemmaDef) -> Result<(), VerificationResult> {
        let load_context = format!("loading lemma `{}`", lemma.name);
        let inserted = self
            .lemmas
            .insert(lemma.name.clone(), lemma.clone())
            .is_none();
        assert!(inserted, "duplicate lemma `{}`", lemma.name);
        let (result, timed_out) = with_z3_deadline(GHOST_LOAD_TIMEOUT, || self.verify_lemma(lemma));
        if timed_out {
            return Err(self.timeout_solver_result(self.report_span(), &load_context));
        }
        result
    }

    pub fn verify_function(
        &mut self,
        def_id: LocalDefId,
        body: Body<'tcx>,
        prepass: DirectivePrepass,
    ) -> VerificationResult {
        self.reset_solver_state();
        let DirectivePrepass {
            loop_contracts,
            control_point_directives,
            function_contract,
            unsafe_blocks,
        } = prepass;
        let contract = function_contract.expect("successful function prepass must yield contract");
        self.contracts.insert(def_id, contract.clone());
        self.context = VerifierContext::Function(FunctionContext {
            def_id,
            body,
            contract,
            loop_contracts,
            control_point_directives,
            unsafe_blocks,
        });

        let initial_state = match self.initial_state() {
            Ok(Some(state)) => state,
            Ok(None) => return self.pass_result("all assertions discharged"),
            Err(err) => return err,
        };
        let mut pending: BTreeMap<ControlPoint, Vec<State>> = BTreeMap::new();
        let mut worklist = VecDeque::new();
        self.enqueue_state(&mut pending, &mut worklist, initial_state);

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
                .control_point_directives()
                .directives_at(ctrl.basic_block, ctrl.statement_index)
            {
                let mut pruned = false;
                for directive in directives {
                    match directive {
                        ControlPointDirective::Let(binding) => {
                            if let Err(err) = self.bind_state_spec_values(
                                &mut state,
                                std::slice::from_ref(&binding.binding),
                                &binding.resolution,
                            ) {
                                return err;
                            }
                        }
                        ControlPointDirective::Assert(assertion) => {
                            if let Err(err) = self.assert_spec_predicate_constraint(
                                &mut state,
                                &assertion.assertion,
                                &assertion.resolution,
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
                            if self.assume_checked_path_condition(&mut state, formula) {
                            } else {
                                pruned = true;
                                break;
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
            if let Some(unsafe_span) = self.unsafe_block_containing_span(self.control_span(ctrl)) {
                let next_states = match self.step_unsafe_region(state, unsafe_span) {
                    Ok(next_states) => next_states,
                    Err(err) => return err,
                };
                for next in next_states {
                    self.enqueue_state(&mut pending, &mut worklist, next);
                }
                continue;
            }

            let data = &self.body().basic_blocks[ctrl.basic_block];
            if ctrl.statement_index < data.statements.len() {
                let stmt = &data.statements[ctrl.statement_index];
                let next = match self.step_statement(state, stmt) {
                    Ok(next) => next,
                    Err(err) => return err,
                };
                self.enqueue_state(&mut pending, &mut worklist, next);
                continue;
            }

            let next_states = match self.step_terminator(state, data.terminator()) {
                Ok(next_states) => next_states,
                Err(err) => return err,
            };
            for next in next_states {
                self.enqueue_state(&mut pending, &mut worklist, next);
            }
        }

        self.pass_result("all assertions discharged")
    }

    fn initial_state(&self) -> Result<Option<State>, VerificationResult> {
        let mut state = State {
            pc: Bool::from_bool(true),
            model: BTreeMap::new(),
            allocs: BTreeMap::new(),
            spec_env: HashMap::new(),
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
            self.create_allocation(&mut state, local, "arg_alloc", self.report_span())?;
        }
        {
            let contract = self.current_contract();
            let env = CallEnv::for_function(self, &state, contract)?;
            state.spec_env =
                self.bind_contract_spec_values(&env.current, &env.spec, &contract.req.bindings)?;
            let env = CallEnv::for_function(self, &state, contract)?;
            let req = self.contract_req_formula(contract, &env, self.report_span())?;
            if !self.assume_path_condition(&mut state, req) {
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
                self.create_allocation(&mut state, *local, "live_alloc", stmt.source_info.span)?;
            }
            StatementKind::StorageDead(local) => {
                let ty = self.body().local_decls[*local].ty;
                if self.ty_contains_mut_ref(ty) {
                    self.resolve_and_remove_local(&mut state, *local, stmt.source_info.span)?;
                }
                state.allocs.remove(local);
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

    fn step_unsafe_statement(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        stmt: &Statement<'tcx>,
    ) -> Result<(), VerificationResult> {
        match &stmt.kind {
            StatementKind::StorageLive(local) => {
                state.store.remove(local);
                self.create_unsafe_allocation(state, *local, "live_alloc", stmt.source_info.span)?;
            }
            StatementKind::StorageDead(local) => {
                state.store.remove(local);
                self.remove_unsafe_local_allocation(state, *local);
            }
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                self.step_unsafe_assign(state, bridge, *place, rvalue, stmt.source_info.span)?;
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
                    format!("unsupported MIR statement in unsafe block {other:?}"),
                ));
            }
        }
        state.ctrl.statement_index += 1;
        Ok(())
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
                {
                    let contract = self.current_contract();
                    let env = CallEnv::for_function(self, &state, contract)?;
                    let ens = self.contract_ens_formula(contract, &env, term.source_info.span)?;
                    self.assert_predicate_constraint(
                        &mut state,
                        ens,
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
                                self.value_is_true(&discr_value).not()
                            } else {
                                self.value_is_true(&discr_value)
                            }
                        }
                        _ => self.eq_for_spec_ty(
                            &self.spec_ty_for_place_ty(
                                discr.ty(&self.body().local_decls, self.tcx),
                                term.source_info.span,
                            )?,
                            &discr_value,
                            &self.value_int(value as i64),
                            term.source_info.span,
                        )?,
                    };
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
                let mut formula = self.value_is_true(&cond_value);
                if !*expected {
                    formula = formula.not();
                }
                self.assert_constraint(
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

    fn step_unsafe_terminator(
        &self,
        mut state: UnsafeState,
        bridge: &UnsafeBridge,
        term: &Terminator<'tcx>,
    ) -> Result<Vec<UnsafeState>, VerificationResult> {
        match &term.kind {
            TerminatorKind::Goto { target } => {
                self.unsafe_goto_target(&mut state, *target);
                Ok(vec![state])
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                msg,
                ..
            } => {
                let cond_value =
                    self.unsafe_eval_operand(&mut state, bridge, cond, term.source_info.span)?;
                let mut formula = self.value_is_true(&cond_value);
                if !*expected {
                    formula = formula.not();
                }
                self.unsafe_assert_constraint(
                    &mut state,
                    formula,
                    term.source_info.span,
                    format!("assertion failed: {msg:?}"),
                )?;
                self.unsafe_goto_target(&mut state, *target);
                Ok(vec![state])
            }
            TerminatorKind::Call { .. } => Err(self.unsupported_result(
                term.source_info.span,
                "function calls inside unsafe blocks are unsupported".to_owned(),
            )),
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_value =
                    self.unsafe_eval_operand(&mut state, bridge, discr, term.source_info.span)?;
                let mut next_states = Vec::new();
                let mut seen_conditions = Vec::new();
                for (value, target) in targets.iter() {
                    let branch = match discr.ty(self.body(), self.tcx).kind() {
                        TyKind::Bool => {
                            if value == 0 {
                                self.value_is_true(&discr_value).not()
                            } else {
                                self.value_is_true(&discr_value)
                            }
                        }
                        _ => self.eq_for_spec_ty(
                            &self.spec_ty_for_place_ty(
                                discr.ty(&self.body().local_decls, self.tcx),
                                term.source_info.span,
                            )?,
                            &discr_value,
                            &self.value_int(value as i64),
                            term.source_info.span,
                        )?,
                    };
                    seen_conditions.push(branch.clone());
                    if let Some(mut next) =
                        self.prune_unsafe_state(state.clone(), branch, term.source_info.span)?
                    {
                        self.unsafe_goto_target(&mut next, target);
                        next_states.push(next);
                    }
                }
                if let Some(mut otherwise) = self.prune_unsafe_state(
                    state,
                    bool_not(bool_or(seen_conditions)),
                    term.source_info.span,
                )? {
                    self.unsafe_goto_target(&mut otherwise, targets.otherwise());
                    next_states.push(otherwise);
                }
                Ok(next_states)
            }
            TerminatorKind::Return => Err(self.unsupported_result(
                term.source_info.span,
                "return inside unsafe blocks is unsupported".to_owned(),
            )),
            other => Err(self.unsupported_result(
                term.source_info.span,
                format!("unsupported MIR terminator in unsafe block {other:?}"),
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
        let callee = self.called_local_def_id(func);
        if let Some(local_def_id) = callee {
            let contract = self
                .contracts
                .get(&local_def_id)
                .ok_or_else(|| self.missing_local_contract_result(local_def_id, span))?;
            let env = self.call_env(&state, args, contract, span, HashMap::new())?;
            let spec =
                self.bind_contract_spec_values(&env.current, &env.spec, &contract.req.bindings)?;
            let req_env = CallEnv {
                current: env.current.clone(),
                spec: spec.clone(),
            };
            let req = self.contract_req_formula(contract, &req_env, span)?;
            self.assert_predicate_constraint(
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
            let ens = self.contract_ens_formula(contract, &env, span)?;
            if !self.assume_path_condition(&mut state, ens) {
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

    fn unsafe_goto_target(&self, state: &mut UnsafeState, target: BasicBlock) {
        state.ctrl = ControlPoint {
            basic_block: target,
            statement_index: 0,
        };
    }

    fn transition_to_block(
        &self,
        mut state: State,
        target: BasicBlock,
        span: Span,
    ) -> Result<Option<State>, VerificationResult> {
        if let Some(loop_contract) = self.loop_contracts().contract_by_header(target) {
            let invariant = self.spec_expr_to_bool(
                &state,
                &loop_contract.invariant,
                &loop_contract.resolution,
            )?;
            self.assert_predicate_constraint(
                &mut state,
                invariant.clone(),
                span,
                loop_contract.invariant_span.clone(),
                "loop invariant does not hold".to_owned(),
            )?;
            let invariant = self.spec_expr_to_bool(
                &state,
                &loop_contract.invariant,
                &loop_contract.resolution,
            )?;
            if self.is_backedge(state.ctrl.basic_block, target, loop_contract) {
                if self.has_loop_marker(&state.pc, target) {
                    return Ok(None);
                }
                let mut abstract_state = state;
                self.havoc_loop_written_locals(&mut abstract_state, loop_contract)?;
                if !self.assume_path_condition(&mut abstract_state, invariant) {
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

        if let Some(header) = self.loop_contracts().header_for_invariant_block(target)
            && let Some(loop_contract) = self.loop_contracts().contract_by_header(header)
        {
            let invariant = self.spec_expr_to_bool(
                &state,
                &loop_contract.invariant,
                &loop_contract.resolution,
            )?;
            if !self.assume_path_condition(&mut state, invariant) {
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
            allocs: BTreeMap::new(),
            spec_env: HashMap::new(),
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

        let shared_allocs: BTreeSet<_> = states
            .iter()
            .map(|state| state.allocs.keys().copied().collect::<BTreeSet<_>>())
            .reduce(|acc, keys| acc.intersection(&keys).copied().collect())
            .unwrap_or_default();
        for local in shared_allocs {
            let incoming_allocs = states
                .iter()
                .map(|state| {
                    state
                        .allocs
                        .get(&local)
                        .cloned()
                        .expect("shared allocation present")
                })
                .collect::<Vec<_>>();
            let first_alloc = incoming_allocs
                .first()
                .cloned()
                .expect("shared allocation present");
            if incoming_allocs
                .iter()
                .all(|alloc| self.allocations_are_identical(alloc, &first_alloc))
            {
                merged.allocs.insert(local, first_alloc);
                continue;
            }

            self.create_allocation(&mut merged, local, "merge_alloc", self.control_span(ctrl))?;
            let merged_alloc = merged
                .allocs
                .get(&local)
                .cloned()
                .expect("merged allocation present");
            for (state, incoming_alloc) in states.iter().zip(incoming_allocs) {
                let equality = self.allocation_equality_formula(
                    &merged_alloc,
                    &incoming_alloc,
                    self.control_span(state.ctrl),
                )?;
                self.add_path_condition(&mut merged, state.pc.clone().implies(equality));
            }
        }

        let shared_spec_names: BTreeSet<_> = states
            .iter()
            .map(|state| state.spec_env.keys().cloned().collect::<BTreeSet<_>>())
            .reduce(|acc, keys| acc.intersection(&keys).cloned().collect())
            .unwrap_or_default();
        for name in shared_spec_names {
            let mut incoming = states
                .iter()
                .map(|state| {
                    state
                        .spec_env
                        .get(&name)
                        .cloned()
                        .expect("shared spec binding present")
                })
                .collect::<Vec<_>>();
            let first = incoming
                .first()
                .cloned()
                .expect("shared spec binding present");
            if incoming.drain(..).all(|value| value == first) {
                merged.spec_env.insert(name, first);
            }
        }

        merged.pc = merged.pc.simplify();
        Ok(Some(merged))
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
            worklist.push_back(ctrl);
        }
        bucket.push(state);
    }

    fn enqueue_unsafe_state(
        &self,
        pending: &mut BTreeMap<ControlPoint, Vec<UnsafeState>>,
        worklist: &mut VecDeque<ControlPoint>,
        state: UnsafeState,
    ) {
        let ctrl = state.ctrl;
        let bucket = pending.entry(ctrl).or_default();
        if bucket.is_empty() {
            worklist.push_back(ctrl);
        }
        bucket.push(state);
    }

    fn step_unsafe_region(
        &self,
        mut state: State,
        unsafe_span: Span,
    ) -> Result<Vec<State>, VerificationResult> {
        let spec_env = std::mem::take(&mut state.spec_env);
        let (unsafe_state, bridge) = self.enter_unsafe(state, unsafe_span)?;
        let mut pending: BTreeMap<ControlPoint, Vec<UnsafeState>> = BTreeMap::new();
        let mut exits: BTreeMap<ControlPoint, Vec<UnsafeState>> = BTreeMap::new();
        let mut worklist = VecDeque::new();
        self.enqueue_unsafe_state(&mut pending, &mut worklist, unsafe_state);

        while let Some(ctrl) = worklist.pop_front() {
            let Some(bucket) = pending.remove(&ctrl) else {
                continue;
            };
            for mut unsafe_state in bucket {
                if !span_contains(unsafe_span, self.control_span(unsafe_state.ctrl)) {
                    exits
                        .entry(unsafe_state.ctrl)
                        .or_default()
                        .push(unsafe_state);
                    continue;
                }

                let data = &self.body().basic_blocks[unsafe_state.ctrl.basic_block];
                if unsafe_state.ctrl.statement_index < data.statements.len() {
                    let statement_index = unsafe_state.ctrl.statement_index;
                    self.step_unsafe_statement(
                        &mut unsafe_state,
                        &bridge,
                        &data.statements[statement_index],
                    )?;
                    self.enqueue_unsafe_state(&mut pending, &mut worklist, unsafe_state);
                } else {
                    for next_state in
                        self.step_unsafe_terminator(unsafe_state, &bridge, data.terminator())?
                    {
                        self.enqueue_unsafe_state(&mut pending, &mut worklist, next_state);
                    }
                }
            }
        }

        let mut next_states = Vec::new();
        for bucket in exits.into_values() {
            for unsafe_state in bucket {
                next_states.push(self.exit_unsafe(unsafe_state, &bridge, spec_env.clone()));
            }
        }
        Ok(next_states)
    }

    fn enter_unsafe(
        &self,
        state: State,
        span: Span,
    ) -> Result<(UnsafeState, UnsafeBridge), VerificationResult> {
        let State {
            pc,
            model,
            allocs,
            ctrl,
            ..
        } = state;
        let reified_allocs = allocs
            .iter()
            .map(|(local, alloc)| (*local, alloc.clone()))
            .collect::<Vec<_>>();
        let mut unsafe_state = UnsafeState {
            pc,
            store: model,
            allocs,
            heap: Vec::new(),
            ctrl,
        };
        let mut bridge = UnsafeBridge::default();

        for (local, alloc) in reified_allocs {
            self.add_unsafe_alloc_resource(&mut unsafe_state, &alloc, span)?;
            bridge.locals.insert(local);
            if let Some(value) = unsafe_state.store.get(&local).cloned() {
                self.write_local_points_to(&mut unsafe_state, local, value, span)?;
            }
        }

        Ok((unsafe_state, bridge))
    }

    fn exit_unsafe(
        &self,
        mut unsafe_state: UnsafeState,
        bridge: &UnsafeBridge,
        spec_env: HashMap<String, SymValue>,
    ) -> State {
        for local in &bridge.locals {
            let ty = self.local_rust_ty_model_value(*local);
            let points_to = unsafe_state
                .allocs
                .get(local)
                .and_then(|alloc| {
                    self.points_to_index_for_ty_value(&unsafe_state, &alloc.base_addr, &ty)
                })
                .map(|index| &unsafe_state.heap[index]);
            match points_to {
                Some(Resource::PointsTo {
                    value: Some(value), ..
                }) => {
                    unsafe_state.store.insert(*local, value.clone());
                }
                Some(Resource::PointsTo { value: None, .. }) | None => {
                    unsafe_state.store.remove(local);
                }
                Some(Resource::Alloc { .. }) => {
                    unreachable!("points_to_index returned an allocation")
                }
            }
        }
        State {
            pc: unsafe_state.pc,
            model: unsafe_state.store,
            allocs: unsafe_state.allocs,
            spec_env,
            ctrl: unsafe_state.ctrl,
        }
    }

    fn create_unsafe_allocation(
        &self,
        state: &mut UnsafeState,
        local: Local,
        hint: &str,
        span: Span,
    ) -> Result<(), VerificationResult> {
        self.remove_unsafe_local_allocation(state, local);
        let ty = self.body().local_decls[local].ty;
        let (size, align) = self.layout_size_align_bytes(ty, span)?;
        let base_addr =
            self.fresh_for_spec_ty(&SpecTy::Usize, &format!("{hint}_{}_base", local.as_usize()))?;
        let alloc = Allocation {
            base_addr,
            size,
            align,
        };

        let other_allocs = state.allocs.values().cloned().collect::<Vec<_>>();
        for other in &other_allocs {
            self.add_unsafe_path_condition(
                state,
                self.allocation_distinct_formula(&alloc, other, span)?,
            );
            if alloc.size != 0 && other.size != 0 {
                self.add_unsafe_path_condition(
                    state,
                    self.allocation_non_overlapping_formula(&alloc, other),
                );
            }
        }
        self.add_unsafe_alloc_resource(state, &alloc, span)?;
        state.allocs.insert(local, alloc);
        Ok(())
    }

    fn add_unsafe_alloc_resource(
        &self,
        state: &mut UnsafeState,
        alloc: &Allocation,
        span: Span,
    ) -> Result<(), VerificationResult> {
        self.add_unsafe_path_condition(state, self.allocation_bounds_formula(alloc, span)?);
        state.heap.push(Resource::Alloc {
            base: alloc.base_addr.clone(),
            size: alloc.size,
            alignment: alloc.align,
        });
        Ok(())
    }

    fn remove_unsafe_local_allocation(&self, state: &mut UnsafeState, local: Local) {
        let local_alloc = state.allocs.remove(&local);
        let ty = self.local_rust_ty_model_value(local);
        state.heap.retain(|resource| match resource {
            Resource::PointsTo {
                addr,
                ty: resource_ty,
                ..
            } => local_alloc
                .as_ref()
                .is_none_or(|alloc| *addr != alloc.base_addr || *resource_ty != ty),
            Resource::Alloc { base, .. } => local_alloc
                .as_ref()
                .is_none_or(|alloc| *base != alloc.base_addr),
        });
    }

    fn write_local_points_to(
        &self,
        state: &mut UnsafeState,
        local: Local,
        value: SymValue,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let alloc = state.allocs.get(&local).cloned().ok_or_else(|| {
            self.unsupported_result(
                span,
                format!("missing allocation for local {}", local.as_usize()),
            )
        })?;
        let ty = self.local_rust_ty_model_value(local);
        if let Some(index) = self.points_to_index_for_ty_value(state, &alloc.base_addr, &ty) {
            if let Resource::PointsTo { value: slot, .. } = &mut state.heap[index] {
                *slot = Some(value);
            }
            return Ok(());
        }

        let addr = alloc.base_addr;
        state.heap.push(Resource::PointsTo {
            addr: addr.clone(),
            ty,
            value: Some(value.clone()),
        });
        let addr_int = self.value_int_data(&addr);
        self.add_unsafe_path_condition(state, addr_int.eq(Int::from_i64(0)).not());
        let ty = self.body().local_decls[local].ty;
        let (_, align) = self.layout_size_align_bytes(ty, span)?;
        if align > 1 {
            self.add_unsafe_path_condition(state, addr_int.modulo(Int::from_u64(align)).eq(0));
        }
        let spec_ty = self.spec_ty_for_place_ty(ty, span)?;
        if let Some(formula) = self.spec_ty_formula(&spec_ty, &value, span)? {
            self.add_unsafe_path_condition(state, formula);
        }
        Ok(())
    }

    fn bridge_local_for_points_to(
        &self,
        state: &UnsafeState,
        bridge: &UnsafeBridge,
        addr: &SymValue,
        ty: &SymValue,
    ) -> Option<Local> {
        bridge.locals.iter().find_map(|local| {
            let alloc = state.allocs.get(local)?;
            if alloc.base_addr == *addr && self.local_rust_ty_model_value(*local) == *ty {
                Some(*local)
            } else {
                None
            }
        })
    }

    fn step_unsafe_assign(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        place: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let value = self.unsafe_eval_rvalue(state, bridge, rvalue, span)?;
        self.unsafe_write_place(state, bridge, place, value, span)
    }

    fn unsafe_eval_rvalue(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        rvalue: &Rvalue<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match rvalue {
            Rvalue::Use(operand) => self.unsafe_eval_operand(state, bridge, operand, span),
            Rvalue::RawPtr(_, place) => self.unsafe_ptr_for_place(state, *place, span),
            Rvalue::Cast(_, operand, target_ty) => {
                self.unsafe_eval_cast(state, bridge, operand, *target_ty, span)
            }
            Rvalue::BinaryOp(op, operands) => {
                let lhs = self.unsafe_eval_operand(state, bridge, &operands.0, span)?;
                let rhs = self.unsafe_eval_operand(state, bridge, &operands.1, span)?;
                let lhs_ty = operands.0.ty(&self.body().local_decls, self.tcx);
                self.lower_unsafe_binary_value(state, *op, lhs_ty, &lhs, &rhs, span)
            }
            Rvalue::UnaryOp(op, operand) => {
                let value = self.unsafe_eval_operand(state, bridge, operand, span)?;
                let operand_ty = operand.ty(&self.body().local_decls, self.tcx);
                self.lower_unsafe_unary_value(state, *op, operand_ty, &value, span)
            }
            Rvalue::Aggregate(kind, operands) => match **kind {
                AggregateKind::Tuple => {
                    let result_ty = self.spec_ty_for_place_ty(
                        rvalue.ty(&self.body().local_decls, self.tcx),
                        span,
                    )?;
                    let mut values = Vec::with_capacity(operands.len());
                    for operand in operands {
                        values.push(self.unsafe_eval_operand(state, bridge, operand, span)?);
                    }
                    self.construct_composite(&result_ty, &values)
                }
                AggregateKind::Adt(def_id, variant_idx, _, _, _) => {
                    let adt_def = self.tcx.adt_def(def_id);
                    if !adt_def.is_struct() || variant_idx.as_usize() != 0 {
                        return Err(self
                            .unsupported_result(span, format!("unsupported aggregate {kind:?}")));
                    }
                    let mut values = Vec::with_capacity(operands.len());
                    for operand in operands {
                        values.push(self.unsafe_eval_operand(state, bridge, operand, span)?);
                    }
                    let result_ty = spec_ty_for_rust_ty(
                        self.tcx,
                        rvalue.ty(&self.body().local_decls, self.tcx),
                    )
                    .map_err(|err| self.unsupported_result(span, err))?;
                    self.construct_composite(&result_ty, &values)
                }
                _ => Err(self.unsupported_result(span, format!("unsupported aggregate {kind:?}"))),
            },
            other => {
                Err(self.unsupported_result(span, format!("unsupported unsafe rvalue {other:?}")))
            }
        }
    }

    fn unsafe_eval_operand(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.unsafe_read_place(state, *place, span)?
            }
            Operand::Constant(constant) => self.eval_const_operand(constant, span)?,
        };
        if let Operand::Constant(constant) = operand {
            self.require_unsafe_type_invariant(
                state,
                constant.const_.ty(),
                &value,
                span,
                "type invariant does not hold".to_owned(),
            )?;
        }
        if matches!(operand, Operand::Move(_)) {
            self.unsafe_consume_operand(state, bridge, operand, span)?;
        }
        Ok(value)
    }

    fn unsafe_eval_cast(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        operand: &Operand<'tcx>,
        target_ty: Ty<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = self.unsafe_eval_operand(state, bridge, operand, span)?;
        match target_ty.kind() {
            TyKind::RawPtr(target_pointee, _) => {
                let operand_ty = operand.ty(&self.body().local_decls, self.tcx);
                let ptr = match operand_ty.kind() {
                    TyKind::RawPtr(_, _) => value,
                    TyKind::Ref(_, inner, mutability) => {
                        let inner_spec_ty = spec_ty_for_rust_ty(self.tcx, *inner)
                            .map_err(|err| self.unsupported_result(span, err))?;
                        if mutability.is_mut() {
                            self.mut_ptr(&value, &inner_spec_ty, span)?
                        } else {
                            self.ref_ptr(&value, &inner_spec_ty, span)?
                        }
                    }
                    TyKind::Uint(_) | TyKind::Int(_) => {
                        return self.ptr_without_provenance(*target_pointee, value);
                    }
                    _ => {
                        return Err(self.unsupported_result(
                            span,
                            format!(
                                "unsupported pointer cast from {operand_ty:?} to {target_ty:?}"
                            ),
                        ));
                    }
                };
                self.ptr_with_ty(&ptr, *target_pointee, span)
            }
            _ => Err(self.unsupported_result(span, format!("unsupported cast to {target_ty:?}"))),
        }
    }

    fn lower_unsafe_binary_value(
        &self,
        state: &mut UnsafeState,
        op: BinOp,
        lhs_ty: Ty<'tcx>,
        lhs: &SymValue,
        rhs: &SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let lhs_spec_ty = self.spec_ty_for_place_ty(lhs_ty, span)?;
        match op {
            BinOp::Add => {
                let value = self.value_int_data(lhs) + self.value_int_data(rhs);
                self.require_unsafe_int_invariant(
                    state,
                    lhs_ty,
                    &value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_encoder.wrap_int(&value))
            }
            BinOp::Sub => {
                let value = self.value_int_data(lhs) - self.value_int_data(rhs);
                self.require_unsafe_int_invariant(
                    state,
                    lhs_ty,
                    &value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_encoder.wrap_int(&value))
            }
            BinOp::Mul => {
                let value = self.value_int_data(lhs) * self.value_int_data(rhs);
                self.require_unsafe_int_invariant(
                    state,
                    lhs_ty,
                    &value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_encoder.wrap_int(&value))
            }
            BinOp::Eq => Ok(self.value_encoder.wrap_bool(&self.eq_for_spec_ty(
                &lhs_spec_ty,
                lhs,
                rhs,
                span,
            )?)),
            BinOp::Ne => Ok(self
                .value_encoder
                .wrap_bool(&self.eq_for_spec_ty(&lhs_spec_ty, lhs, rhs, span)?.not())),
            BinOp::Lt => Ok(self
                .value_encoder
                .wrap_bool(&self.value_int_data(lhs).lt(self.value_int_data(rhs)))),
            BinOp::Le => Ok(self
                .value_encoder
                .wrap_bool(&self.value_int_data(lhs).le(self.value_int_data(rhs)))),
            BinOp::Gt => Ok(self
                .value_encoder
                .wrap_bool(&self.value_int_data(lhs).gt(self.value_int_data(rhs)))),
            BinOp::Ge => Ok(self
                .value_encoder
                .wrap_bool(&self.value_int_data(lhs).ge(self.value_int_data(rhs)))),
            other => {
                Err(self.unsupported_result(span, format!("unsupported binary operator {other:?}")))
            }
        }
    }

    fn lower_unsafe_unary_value(
        &self,
        state: &mut UnsafeState,
        op: UnOp,
        operand_ty: Ty<'tcx>,
        value: &SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match op {
            UnOp::Not => Ok(self
                .value_encoder
                .wrap_bool(&self.value_is_true(value).not())),
            UnOp::Neg => {
                let int_value = Int::from_i64(0) - self.value_int_data(value);
                self.require_unsafe_int_invariant(
                    state,
                    operand_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_encoder.wrap_int(&int_value))
            }
            other => {
                Err(self.unsupported_result(span, format!("unsupported unary operator {other:?}")))
            }
        }
    }

    fn unsafe_ptr_for_place(
        &self,
        state: &mut UnsafeState,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let projection = place.as_ref().projection;
        let final_ty = self.place_ty(place);
        if matches!(projection.first(), Some(PlaceElem::Deref)) {
            let Some(root) = state.store.get(&place.local).cloned() else {
                return Err(self.unsupported_result(
                    span,
                    format!("missing local {}", place.local.as_usize()),
                ));
            };
            let root_ty = self.body().local_decls[place.local].ty;
            let root_spec_ty = self.spec_ty_for_place_ty(root_ty, span)?;
            let base_ptr = self.ptr_for_deref_base(&root, &root_spec_ty, span)?;
            let pointee_ty = self.deref_pointee_ty(root_ty, span)?;
            return self.ptr_for_base_projection(
                &base_ptr,
                pointee_ty,
                &projection[1..],
                final_ty,
                span,
            );
        }

        let alloc = state.allocs.get(&place.local).ok_or_else(|| {
            self.unsupported_result(
                span,
                format!("missing allocation for local {}", place.local.as_usize()),
            )
        })?;
        let root_ty = self.body().local_decls[place.local].ty;
        let offset = self.place_projection_offset(root_ty, projection, span)?;
        let addr = self.add_addr_offset(alloc.base_addr.clone(), offset);
        let provenance = self.construct_provenance(alloc.base_addr.clone())?;
        let prov = self.construct_option_some(provenance_spec_ty(), provenance)?;
        let ty = self.rust_ty_model_value(final_ty);
        self.construct_ptr(addr, prov, ty)
    }

    fn unsafe_read_place(
        &self,
        state: &mut UnsafeState,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let projection = place.as_ref().projection;
        let root_ty = self.body().local_decls[place.local].ty;
        let Some(root) = state.store.get(&place.local).cloned() else {
            return Err(
                self.unsupported_result(span, format!("missing local {}", place.local.as_usize()))
            );
        };
        if matches!(projection.first(), Some(PlaceElem::Deref))
            && matches!(root_ty.kind(), TyKind::RawPtr(_, _))
        {
            let pointee_ty = self.deref_pointee_ty(root_ty, span)?;
            let value = self.unsafe_read_raw_pointer(state, &root, pointee_ty, span)?;
            let pointee_spec_ty = self.spec_ty_for_place_ty(pointee_ty, span)?;
            return self.read_projection(
                value,
                &pointee_spec_ty,
                &projection[1..],
                ReadMode::Current,
                span,
            );
        }

        let root_spec_ty = self.spec_ty_for_place_ty(root_ty, span)?;
        self.read_projection(root, &root_spec_ty, projection, ReadMode::Current, span)
    }

    fn unsafe_write_place(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        place: Place<'tcx>,
        value: SymValue,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let projection = place.as_ref().projection;
        let root_ty = self.body().local_decls[place.local].ty;
        if matches!(projection.first(), Some(PlaceElem::Deref))
            && matches!(root_ty.kind(), TyKind::RawPtr(_, _))
        {
            let ptr = state.store.get(&place.local).cloned().ok_or_else(|| {
                self.unsupported_result(span, format!("missing local {}", place.local.as_usize()))
            })?;
            let pointee_ty = self.deref_pointee_ty(root_ty, span)?;
            let replacement = if projection.len() == 1 {
                value
            } else {
                let current = self.unsafe_read_raw_pointer(state, &ptr, pointee_ty, span)?;
                let pointee_spec_ty = self.spec_ty_for_place_ty(pointee_ty, span)?;
                self.write_projection(current, &pointee_spec_ty, &projection[1..], value, span)?
            };
            return self.unsafe_write_raw_pointer(
                state,
                bridge,
                &ptr,
                pointee_ty,
                replacement,
                span,
            );
        }

        let root = state
            .store
            .get(&place.local)
            .cloned()
            .unwrap_or_else(|| value.clone());
        let root_spec_ty = self.spec_ty_for_place_ty(root_ty, span)?;
        let updated = self.write_projection(root, &root_spec_ty, projection, value, span)?;
        state.store.insert(place.local, updated.clone());
        self.write_local_points_to(state, place.local, updated, span)?;
        Ok(())
    }

    fn unsafe_consume_operand(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        operand: &Operand<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        match operand {
            Operand::Copy(_) | Operand::Constant(_) => Ok(()),
            Operand::Move(place) => {
                if self.place_starts_with_raw_pointer_deref(*place) {
                    let root = state.store.get(&place.local).cloned().ok_or_else(|| {
                        self.unsupported_result(
                            span,
                            format!("missing local {}", place.local.as_usize()),
                        )
                    })?;
                    let root_ty = self.body().local_decls[place.local].ty;
                    let pointee_ty = self.deref_pointee_ty(root_ty, span)?;
                    self.unsafe_deinit_raw_pointer(state, bridge, &root, pointee_ty, span)
                } else if place.projection.is_empty() {
                    state.store.remove(&place.local);
                    self.deinit_local_points_to(state, place.local);
                    Ok(())
                } else {
                    let value = self.unsafe_read_place(state, *place, span)?;
                    let place_ty = self.spec_ty_for_place_ty(self.place_ty(*place), span)?;
                    let updated = self.dangle_value(&place_ty, &value, span)?;
                    self.unsafe_write_place(state, bridge, *place, updated, span)
                }
            }
        }
    }

    fn unsafe_read_raw_pointer(
        &self,
        state: &mut UnsafeState,
        ptr: &SymValue,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        self.assert_raw_pointer_deref_preconditions(state, ptr, ty, true, span)?;
        let addr = self.ptr_addr(ptr, span)?;
        let value = self.read_matching_points_to(state, &addr, ty, span)?;
        self.require_unsafe_type_invariant(
            state,
            ty,
            &value,
            span,
            "raw pointer read produced an invalid typed value".to_owned(),
        )?;
        Ok(value)
    }

    fn unsafe_write_raw_pointer(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        ptr: &SymValue,
        ty: Ty<'tcx>,
        value: SymValue,
        span: Span,
    ) -> Result<(), VerificationResult> {
        self.assert_raw_pointer_deref_preconditions(state, ptr, ty, false, span)?;
        self.require_unsafe_type_invariant(
            state,
            ty,
            &value,
            span,
            "raw pointer write requires a valid typed value".to_owned(),
        )?;
        let addr = self.ptr_addr(ptr, span)?;
        self.write_matching_points_to(state, bridge, &addr, ty, value, span)
    }

    fn unsafe_deinit_raw_pointer(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        ptr: &SymValue,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        self.assert_raw_pointer_deref_preconditions(state, ptr, ty, false, span)?;
        let addr = self.ptr_addr(ptr, span)?;
        self.deinit_matching_points_to(state, bridge, &addr, ty, span)
    }

    fn assert_raw_pointer_deref_preconditions(
        &self,
        state: &mut UnsafeState,
        ptr: &SymValue,
        ty: Ty<'tcx>,
        require_initialized_points_to: bool,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let addr = self.ptr_addr(ptr, span)?;
        let actual_ty = self.ptr_ty(ptr, span)?;
        let expected_ty = self.rust_ty_model_value(ty);
        let ptr_ty_matches =
            self.eq_for_spec_ty(&SpecTy::RustTy, &actual_ty, &expected_ty, span)?;
        let addr_int = self.value_int_data(&addr);
        let non_null = addr_int.eq(Int::from_i64(0)).not();
        if matches!(non_null.simplify().as_bool(), Some(false)) {
            return Err(self.fail_result(
                span,
                "raw pointer dereference requires a non-null address".to_owned(),
            ));
        }
        let (_, align) = self.layout_size_align_bytes(ty, span)?;
        let aligned = if align > 1 {
            Some(addr_int.modulo(Int::from_u64(align)).eq(0))
        } else {
            None
        };
        if matches!(
            aligned
                .as_ref()
                .and_then(|formula| formula.simplify().as_bool()),
            Some(false)
        ) {
            return Err(self.fail_result(
                span,
                "raw pointer dereference requires proper alignment".to_owned(),
            ));
        }
        if matches!(ptr_ty_matches.simplify().as_bool(), Some(false)) {
            return Err(self.fail_result(
                span,
                "raw pointer type does not match the dereferenced type".to_owned(),
            ));
        }
        let points_to_exists = self.points_to_coverage_formula(
            state,
            &addr,
            &expected_ty,
            require_initialized_points_to,
            span,
        )?;
        self.unsafe_assert_memory_precondition(
            state,
            points_to_exists,
            span,
            "raw pointer dereference requires an initialized PointsTo resource".to_owned(),
        )?;
        self.unsafe_assert_memory_precondition(
            state,
            ptr_ty_matches,
            span,
            "raw pointer type does not match the dereferenced type".to_owned(),
        )?;
        self.unsafe_assert_memory_precondition(
            state,
            non_null,
            span,
            "raw pointer dereference requires a non-null address".to_owned(),
        )?;
        if align > 1 {
            self.unsafe_assert_memory_precondition(
                state,
                aligned.expect("computed above"),
                span,
                "raw pointer dereference requires proper alignment".to_owned(),
            )?;
        }
        let live_range = self.unsafe_live_allocation_formula(state, ptr, &addr, ty, span)?;
        self.unsafe_assert_memory_precondition(
            state,
            live_range,
            span,
            "raw pointer dereference requires a live allocation covering the value".to_owned(),
        )
    }

    fn unsafe_live_allocation_formula(
        &self,
        state: &UnsafeState,
        ptr: &SymValue,
        addr: &SymValue,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let (size, _) = self.layout_size_align_bytes(ty, span)?;
        let addr_int = self.value_int_data(addr);
        let ptr_prov = self.ptr_prov(ptr, span)?;
        let end = addr_int.clone() + Int::from_u64(size);
        let mut candidates = Vec::new();
        for resource in &state.heap {
            let Resource::Alloc {
                base,
                size,
                alignment,
            } = resource
            else {
                continue;
            };
            let base_int = self.value_int_data(base);
            let alloc_end = base_int.clone() + Int::from_u64(*size);
            let provenance = self.construct_provenance(base.clone())?;
            let expected_prov = self.construct_option_some(provenance_spec_ty(), provenance)?;
            let prov_matches = self.eq_for_spec_ty(
                &option_spec_ty(provenance_spec_ty()),
                &ptr_prov,
                &expected_prov,
                span,
            )?;
            let mut formulas = vec![
                prov_matches,
                addr_int.ge(base_int.clone()),
                end.le(alloc_end),
            ];
            if *alignment > 1 {
                formulas.push(base_int.modulo(Int::from_u64(*alignment)).eq(0));
            }
            candidates.push(bool_and(formulas));
        }
        Ok(bool_or(candidates))
    }

    fn points_to_coverage_formula(
        &self,
        state: &UnsafeState,
        addr: &SymValue,
        ty: &SymValue,
        require_initialized: bool,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        Ok(bool_or(
            self.points_to_match_conditions_for_ty_value(
                state,
                addr,
                ty,
                require_initialized,
                span,
            )?
            .into_iter()
            .map(|(_, condition)| condition)
            .collect(),
        ))
    }

    fn points_to_match_conditions(
        &self,
        state: &UnsafeState,
        addr: &SymValue,
        ty: Ty<'tcx>,
        require_initialized: bool,
        span: Span,
    ) -> Result<Vec<(usize, Bool)>, VerificationResult> {
        let ty = self.rust_ty_model_value(ty);
        self.points_to_match_conditions_for_ty_value(state, addr, &ty, require_initialized, span)
    }

    fn points_to_match_conditions_for_ty_value(
        &self,
        state: &UnsafeState,
        addr: &SymValue,
        ty: &SymValue,
        require_initialized: bool,
        span: Span,
    ) -> Result<Vec<(usize, Bool)>, VerificationResult> {
        let mut candidates = Vec::new();
        for (index, resource) in state.heap.iter().enumerate() {
            let Resource::PointsTo {
                addr: resource_addr,
                ty: resource_ty,
                value,
            } = resource
            else {
                continue;
            };
            if require_initialized && value.is_none() {
                continue;
            }
            if resource_ty != ty {
                continue;
            }
            let addr_matches = self.eq_for_spec_ty(&SpecTy::Usize, addr, resource_addr, span)?;
            let condition = addr_matches.simplify();
            if matches!(condition.as_bool(), Some(false)) {
                continue;
            }
            if !matches!(
                self.check_sat(&[state.pc.clone(), condition.clone()]),
                SatResult::Unsat
            ) {
                candidates.push((index, condition));
            }
        }
        Ok(candidates)
    }

    fn read_matching_points_to(
        &self,
        state: &mut UnsafeState,
        addr: &SymValue,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let candidates = self.points_to_match_conditions(state, addr, ty, true, span)?;
        if candidates.is_empty() {
            return Err(self.missing_points_to_result(span));
        }
        if candidates.len() == 1
            && matches!(candidates[0].1.simplify().as_bool(), Some(true))
            && let Resource::PointsTo {
                value: Some(value), ..
            } = &state.heap[candidates[0].0]
        {
            return Ok(value.clone());
        }

        let value = self.fresh_for_rust_ty(ty, "unsafe_read")?;
        let spec_ty = self.spec_ty_for_place_ty(ty, span)?;
        for (index, condition) in candidates {
            let Resource::PointsTo {
                value: Some(resource_value),
                ..
            } = &state.heap[index]
            else {
                continue;
            };
            let equality = self.eq_for_spec_ty(&spec_ty, &value, resource_value, span)?;
            self.add_unsafe_path_condition(state, condition.implies(equality));
        }
        Ok(value)
    }

    fn write_matching_points_to(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        addr: &SymValue,
        ty: Ty<'tcx>,
        value: SymValue,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let candidates = self.points_to_match_conditions(state, addr, ty, false, span)?;
        if candidates.is_empty() {
            return Err(self.missing_points_to_result(span));
        }
        let mut updates = Vec::new();
        for (index, condition) in candidates {
            let Resource::PointsTo {
                addr: resource_addr,
                ty: resource_ty,
                value: old_value,
            } = &state.heap[index]
            else {
                unreachable!("points-to candidate must be PointsTo");
            };
            let local = self.bridge_local_for_points_to(state, bridge, resource_addr, resource_ty);
            updates.push((index, condition, old_value.clone(), local));
        }

        for (index, condition, old_value, local) in updates {
            let replacement =
                self.conditional_points_to_value(state, condition, old_value, &value, ty, span)?;
            if let Resource::PointsTo { value: slot, .. } = &mut state.heap[index] {
                *slot = replacement.clone();
            }
            if let Some(local) = local {
                match replacement {
                    Some(value) => {
                        state.store.insert(local, value);
                    }
                    None => {
                        state.store.remove(&local);
                    }
                }
            }
        }
        Ok(())
    }

    fn deinit_matching_points_to(
        &self,
        state: &mut UnsafeState,
        bridge: &UnsafeBridge,
        addr: &SymValue,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let candidates = self.points_to_match_conditions(state, addr, ty, false, span)?;
        if candidates.is_empty() {
            return Err(self.missing_points_to_result(span));
        }
        let mut updates = Vec::new();
        for (index, condition) in candidates {
            let Resource::PointsTo {
                addr: resource_addr,
                ty: resource_ty,
                ..
            } = &state.heap[index]
            else {
                unreachable!("points-to candidate must be PointsTo");
            };
            let local = self.bridge_local_for_points_to(state, bridge, resource_addr, resource_ty);
            updates.push((index, condition, local));
        }

        for (index, condition, local) in updates {
            if !self.unsafe_path_implies(state, &condition) {
                return Err(self.unsupported_result(
                    span,
                    "conditional deinitialization through a raw pointer is unsupported".to_owned(),
                ));
            }
            if let Resource::PointsTo { value, .. } = &mut state.heap[index] {
                *value = None;
            }
            if let Some(local) = local {
                state.store.remove(&local);
            }
        }
        Ok(())
    }

    fn conditional_points_to_value(
        &self,
        state: &mut UnsafeState,
        condition: Bool,
        old_value: Option<SymValue>,
        value: &SymValue,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<Option<SymValue>, VerificationResult> {
        let condition = condition.simplify();
        if matches!(condition.as_bool(), Some(false)) {
            return Ok(old_value);
        }
        if self.unsafe_path_implies(state, &condition) {
            return Ok(Some(value.clone()));
        }
        let Some(old_value) = old_value else {
            return Err(self.unsupported_result(
                span,
                "conditional initialization through a raw pointer is unsupported".to_owned(),
            ));
        };
        let result = self.fresh_for_rust_ty(ty, "unsafe_write")?;
        let spec_ty = self.spec_ty_for_place_ty(ty, span)?;
        let new_equality = self.eq_for_spec_ty(&spec_ty, &result, value, span)?;
        self.add_unsafe_path_condition(state, condition.clone().implies(new_equality));
        let old_equality = self.eq_for_spec_ty(&spec_ty, &result, &old_value, span)?;
        self.add_unsafe_path_condition(state, condition.not().implies(old_equality));
        Ok(Some(result))
    }

    fn unsafe_path_implies(&self, state: &UnsafeState, condition: &Bool) -> bool {
        matches!(
            self.check_sat(&[state.pc.clone(), condition.not()]),
            SatResult::Unsat
        )
    }

    fn points_to_index_for_ty_value(
        &self,
        state: &UnsafeState,
        addr: &SymValue,
        ty: &SymValue,
    ) -> Option<usize> {
        state.heap.iter().position(|resource| {
            matches!(
                resource,
                Resource::PointsTo {
                    addr: resource_addr,
                    ty: resource_ty,
                    ..
                } if resource_addr == addr && resource_ty == ty
            )
        })
    }

    fn deinit_local_points_to(&self, state: &mut UnsafeState, local: Local) {
        let Some(alloc) = state.allocs.get(&local) else {
            return;
        };
        let ty = self.local_rust_ty_model_value(local);
        if let Some(index) = self.points_to_index_for_ty_value(state, &alloc.base_addr, &ty)
            && let Resource::PointsTo { value, .. } = &mut state.heap[index]
        {
            *value = None;
        }
    }

    fn place_starts_with_raw_pointer_deref(&self, place: Place<'tcx>) -> bool {
        matches!(place.as_ref().projection.first(), Some(PlaceElem::Deref))
            && matches!(
                self.body().local_decls[place.local].ty.kind(),
                TyKind::RawPtr(_, _)
            )
    }

    fn unsafe_assert_constraint(
        &self,
        state: &mut UnsafeState,
        constraint: Bool,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let constraint = constraint.simplify();
        if let Some(value) = constraint.as_bool() {
            return match value {
                true => {
                    self.add_unsafe_path_condition(state, constraint);
                    Ok(())
                }
                false => Err(self.fail_result(span, message)),
            };
        }
        match self.check_sat(&[state.pc.clone(), constraint.not()]) {
            SatResult::Sat => Err(self.fail_result(span, message)),
            SatResult::Unsat => {
                self.add_unsafe_path_condition(state, constraint);
                Ok(())
            }
            SatResult::Unknown => Err(self.unknown_solver_result(span, "checking unsafe code")),
        }
    }

    fn unsafe_assert_memory_precondition(
        &self,
        state: &mut UnsafeState,
        constraint: Bool,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let constraint = constraint.simplify();
        if let Some(value) = constraint.as_bool() {
            return match value {
                true => {
                    self.add_unsafe_path_condition(state, constraint);
                    Ok(())
                }
                false => Err(self.fail_result(span, message)),
            };
        }
        match self.check_sat(&[state.pc.clone(), constraint.not()]) {
            SatResult::Sat | SatResult::Unknown => Err(self.fail_result(span, message)),
            SatResult::Unsat => {
                self.add_unsafe_path_condition(state, constraint);
                Ok(())
            }
        }
    }

    fn add_unsafe_path_condition(&self, state: &mut UnsafeState, constraint: Bool) {
        state.pc = bool_and(vec![state.pc.clone(), constraint]).simplify();
    }

    fn require_unsafe_type_invariant(
        &self,
        state: &mut UnsafeState,
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
        self.unsafe_assert_constraint(state, formula, span, message)
    }

    fn require_unsafe_int_invariant(
        &self,
        state: &mut UnsafeState,
        ty: Ty<'tcx>,
        value: &Int,
        span: Span,
        message: String,
    ) -> Result<(), VerificationResult> {
        let Some((lower, upper)) = self.int_bounds_for_rust_ty(ty, span)? else {
            return Ok(());
        };
        self.unsafe_assert_constraint(
            state,
            bool_and(vec![value.ge(lower), value.le(upper)]),
            span,
            message,
        )
    }

    fn missing_points_to_result(&self, span: Span) -> VerificationResult {
        self.fail_result(
            span,
            "raw pointer dereference requires an initialized PointsTo resource".to_owned(),
        )
    }

    fn register_pure_fn(&mut self, pure_fn: &TypedPureFnDef) -> Result<(), VerificationResult> {
        let domain_sorts = pure_fn
            .params
            .iter()
            .map(|param| {
                self.type_encoding(&param.ty)
                    .map(|encoding| encoding.sort.clone())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let domain_refs: Vec<_> = domain_sorts.iter().collect();
        let result_sort = self.type_encoding(&pure_fn.body.ty)?.sort.clone();
        let decl = RecFuncDecl::new(
            format!("pure_fn_{}", pure_fn.name),
            &domain_refs,
            &result_sort,
        );
        let inserted = self
            .pure_fn_decls
            .insert(pure_fn.name.clone(), decl)
            .is_none();
        assert!(inserted, "duplicate pure function decl `{}`", pure_fn.name);
        let mut current = HashMap::new();
        let mut vars = Vec::with_capacity(pure_fn.params.len());
        for param in &pure_fn.params {
            let sort = self.type_encoding(&param.ty)?.sort.clone();
            let value = SymValue::new(Dynamic::new_const(
                self.fresh_name(&format!("pure_{}_{}", pure_fn.name, param.name)),
                &sort,
            ));
            current.insert(param.name.clone(), value.clone());
            vars.push(value);
        }
        let spec = HashMap::new();
        let body = self.contract_expr_to_value(&current, &spec, &pure_fn.body)?;
        let args: Vec<&dyn Ast> = vars.iter().map(SymValue::ast).collect();
        let decl = self
            .pure_fn_decls
            .get(&pure_fn.name)
            .expect("pure function decl must be inserted before lowering the body");
        decl.add_def(&args, body.dynamic());
        Ok(())
    }

    fn verify_lemma(&self, lemma: &TypedLemmaDef) -> Result<(), VerificationResult> {
        let mut current = HashMap::new();
        for param in &lemma.params {
            let value =
                self.fresh_for_spec_ty(&param.ty, &format!("lemma_{}_{}", lemma.name, param.name))?;
            current.insert(param.name.clone(), value);
        }
        let mut state = State {
            pc: Bool::from_bool(true),
            model: BTreeMap::new(),
            allocs: BTreeMap::new(),
            spec_env: HashMap::new(),
            ctrl: ControlPoint {
                basic_block: BasicBlock::from_usize(0),
                statement_index: 0,
            },
        };
        let state_spec = state.spec_env.clone();
        let Some(spec) =
            self.assume_contract_predicate(&mut state, &lemma.req, &current, &state_spec)?
        else {
            return Ok(());
        };
        state.spec_env = spec;
        for param in &lemma.params {
            let value = current.get(&param.name).expect("lemma parameter value");
            if let Some(formula) = self.spec_ty_formula(&param.ty, value, self.report_span())?
                && !self.assume_path_condition(&mut state, formula)
            {
                return Ok(());
            }
        }
        let final_states = self.execute_lemma_stmts(lemma, &current, state, &lemma.body)?;
        for final_exec in final_states {
            let mut final_state = final_exec.state;
            let ens =
                self.contract_expr_to_bool(&final_exec.current, &final_state.spec_env, &lemma.ens)?;
            self.assert_predicate_constraint(
                &mut final_state,
                ens,
                self.report_span(),
                format!("lemma `{}`", lemma.name),
                format!("lemma `{}` postcondition failed", lemma.name),
            )?;
        }
        Ok(())
    }

    fn execute_lemma_stmts(
        &self,
        lemma: &TypedLemmaDef,
        current: &HashMap<String, SymValue>,
        mut state: State,
        stmts: &[TypedGhostStmt],
    ) -> Result<Vec<LemmaExecState>, VerificationResult> {
        let Some((stmt, rest)) = stmts.split_first() else {
            return Ok(vec![LemmaExecState {
                current: current.clone(),
                state,
            }]);
        };
        match stmt {
            TypedGhostStmt::Assert(expr) => {
                let state_spec = state.spec_env.clone();
                let spec = self.assert_contract_predicate_constraint(
                    &mut state,
                    expr,
                    current,
                    &state_spec,
                    self.report_span(),
                    format!("lemma `{}`", lemma.name),
                    format!("lemma `{}` assertion failed", lemma.name),
                )?;
                state.spec_env = spec;
                self.execute_lemma_stmts(lemma, current, state, rest)
            }
            TypedGhostStmt::Assume(expr) => {
                let formula = self.contract_expr_to_bool(current, &state.spec_env, expr)?;
                if !self.assume_path_condition(&mut state, formula) {
                    return Ok(Vec::new());
                }
                self.execute_lemma_stmts(lemma, current, state, rest)
            }
            TypedGhostStmt::Call { lemma_name, args } => {
                let callee = self.lemmas.get(lemma_name).ok_or_else(|| {
                    self.unsupported_result(
                        self.report_span(),
                        format!("unknown lemma `{lemma_name}`"),
                    )
                })?;
                let env =
                    self.lemma_env_from_contract_args(args, current, &state.spec_env, callee)?;
                let spec = self.assert_contract_predicate_constraint(
                    &mut state,
                    &callee.req,
                    &env.current,
                    &env.spec,
                    self.report_span(),
                    format!("lemma `{}`", lemma.name),
                    format!("lemma `{}` precondition failed", callee.name),
                )?;
                let ens = self.contract_expr_to_bool(&env.current, &spec, &callee.ens)?;
                if !self.assume_path_condition(&mut state, ens) {
                    return Ok(Vec::new());
                }
                self.execute_lemma_stmts(lemma, current, state, rest)
            }
            TypedGhostStmt::Match {
                scrutinee,
                arms,
                default,
            } => self.execute_lemma_match(
                lemma,
                current,
                state,
                scrutinee,
                arms,
                default.as_deref(),
                rest,
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn execute_lemma_match(
        &self,
        lemma: &TypedLemmaDef,
        current: &HashMap<String, SymValue>,
        state: State,
        scrutinee: &TypedExpr,
        arms: &[TypedGhostMatchArm],
        default: Option<&[TypedGhostStmt]>,
        rest: &[TypedGhostStmt],
    ) -> Result<Vec<LemmaExecState>, VerificationResult> {
        let scrutinee_value = self.contract_expr_to_value(current, &state.spec_env, scrutinee)?;
        let composite = self.composite_encoding(&scrutinee.ty)?;
        let mut guard_formulas = Vec::with_capacity(arms.len());
        let mut final_states = Vec::new();
        for arm in arms {
            let mut branch_state = state.clone();
            let guard = self.composite_tag_formula_for_encoding(
                &composite,
                &scrutinee_value,
                arm.ctor_index,
                self.report_span(),
            )?;
            guard_formulas.push(guard.clone());
            if !self.assume_path_condition(&mut branch_state, guard) {
                continue;
            }
            let mut branch_current = current.clone();
            let mut field_values = Vec::with_capacity(arm.bindings.len());
            for (field_index, binding) in arm.bindings.iter().enumerate() {
                let field_value = self
                    .value_encoder
                    .project_composite_ctor_field(
                        &composite,
                        arm.ctor_index,
                        &scrutinee_value,
                        field_index,
                    )
                    .map_err(|err| self.unsupported_result(self.report_span(), err))?;
                if let TypedMatchBinding::Var { name, .. } = binding {
                    branch_current.insert(name.clone(), field_value.clone());
                }
                field_values.push(field_value);
            }
            let ctor_value =
                self.construct_composite_ctor(&scrutinee.ty, arm.ctor_index, &field_values)?;
            if let TypedExprKind::Var(name) = &scrutinee.kind {
                branch_current.insert(name.clone(), ctor_value.clone());
            }
            let branch_eq = self.eq_for_spec_ty(
                &scrutinee.ty,
                &scrutinee_value,
                &ctor_value,
                self.report_span(),
            )?;
            if !self.assume_path_condition(&mut branch_state, branch_eq) {
                continue;
            }
            let branch_end_states =
                self.execute_lemma_stmts(lemma, &branch_current, branch_state, &arm.body)?;
            for branch_end_state in branch_end_states {
                final_states.extend(self.execute_lemma_stmts(
                    lemma,
                    &branch_end_state.current,
                    branch_end_state.state,
                    rest,
                )?);
            }
        }
        if let Some(default) = default {
            let mut default_state = state;
            let default_guard = bool_and(guard_formulas.into_iter().map(bool_not).collect());
            if self.assume_path_condition(&mut default_state, default_guard) {
                let default_end_states =
                    self.execute_lemma_stmts(lemma, current, default_state, default)?;
                for default_end_state in default_end_states {
                    final_states.extend(self.execute_lemma_stmts(
                        lemma,
                        &default_end_state.current,
                        default_end_state.state,
                        rest,
                    )?);
                }
            }
        }
        Ok(final_states)
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
        let spec = self.assert_contract_predicate_constraint(
            state,
            &lemma.req,
            &env.current,
            &env.spec,
            span,
            call.span_text.clone(),
            format!("lemma `{}` precondition failed", lemma.name),
        )?;
        let ens = self.contract_expr_to_bool(&env.current, &spec, &lemma.ens)?;
        Ok(self.assume_path_condition(state, ens))
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
            spec: state.spec_env.clone(),
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
            spec: spec.clone(),
        })
    }

    fn resolve_and_remove_local(
        &self,
        state: &mut State,
        local: Local,
        span: Span,
    ) -> Result<(), VerificationResult> {
        state.allocs.remove(&local);
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
            Rvalue::RawPtr(_, place) => self.ptr_for_place(state, *place, span),
            Rvalue::Cast(_, operand, target_ty) => self.eval_cast(state, operand, *target_ty, span),
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
                    self.construct_composite(&result_ty, &values)
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
                    self.construct_composite(&result_ty, &values)
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
        let place_ty = self.place_ty(place);
        let inner_ty = self.spec_ty_for_place_ty(place_ty, span)?;
        let ptr = self.ptr_for_place(state, place, span)?;
        self.construct_composite(
            &SpecTy::Mut(Box::new(inner_ty)),
            &[current, final_value, ptr],
        )
    }

    fn create_shared_borrow(
        &self,
        state: &State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = self.read_place(state, place, ReadMode::Current, span)?;
        let place_ty = self.place_ty(place);
        let inner_ty = self.spec_ty_for_place_ty(place_ty, span)?;
        let ptr = self.ptr_for_place(state, place, span)?;
        self.construct_composite(&SpecTy::Ref(Box::new(inner_ty)), &[value, ptr])
    }

    fn eval_cast(
        &self,
        state: &mut State,
        operand: &Operand<'tcx>,
        target_ty: Ty<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let value = self.eval_operand(state, operand, span)?;
        match target_ty.kind() {
            TyKind::RawPtr(target_pointee, _) => {
                let operand_ty = operand.ty(&self.body().local_decls, self.tcx);
                let ptr = match operand_ty.kind() {
                    TyKind::RawPtr(_, _) => value,
                    TyKind::Ref(_, inner, mutability) => {
                        let inner_spec_ty = spec_ty_for_rust_ty(self.tcx, *inner)
                            .map_err(|err| self.unsupported_result(span, err))?;
                        if mutability.is_mut() {
                            self.mut_ptr(&value, &inner_spec_ty, span)?
                        } else {
                            self.ref_ptr(&value, &inner_spec_ty, span)?
                        }
                    }
                    TyKind::Uint(_) | TyKind::Int(_) => {
                        return self.ptr_without_provenance(*target_pointee, value);
                    }
                    _ => {
                        return Err(self.unsupported_result(
                            span,
                            format!(
                                "unsupported pointer cast from {operand_ty:?} to {target_ty:?}"
                            ),
                        ));
                    }
                };
                self.ptr_with_ty(&ptr, *target_pointee, span)
            }
            _ => Err(self.unsupported_result(span, format!("unsupported cast to {target_ty:?}"))),
        }
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
                Ok(self.value_encoder.wrap_int(&int_value))
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
                Ok(self.value_encoder.wrap_int(&int_value))
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
                Ok(self.value_encoder.wrap_int(&int_value))
            }
            BinOp::Eq => Ok(self.value_encoder.wrap_bool(&self.eq_for_spec_ty(
                &lhs_spec_ty,
                &lhs_value,
                &rhs_value,
                span,
            )?)),
            BinOp::Ne => Ok(self.value_encoder.wrap_bool(
                &self
                    .eq_for_spec_ty(&lhs_spec_ty, &lhs_value, &rhs_value, span)?
                    .not(),
            )),
            BinOp::Lt => Ok(self.value_encoder.wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .lt(self.value_int_data(&rhs_value)),
            )),
            BinOp::Le => Ok(self.value_encoder.wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .le(self.value_int_data(&rhs_value)),
            )),
            BinOp::Gt => Ok(self.value_encoder.wrap_bool(
                &self
                    .value_int_data(&lhs_value)
                    .gt(self.value_int_data(&rhs_value)),
            )),
            BinOp::Ge => Ok(self.value_encoder.wrap_bool(
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
                self.value_encoder.wrap_int(&int_value)
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
                self.value_encoder.wrap_int(&int_value)
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
                self.value_encoder.wrap_int(&int_value)
            }
            other => {
                return Err(self.unsupported_result(
                    span,
                    format!("unsupported checked binary operator {other:?}"),
                ));
            }
        };
        let overflow_value = self.overflow_value_for_result(result_ty, &result_value, span)?;
        self.construct_composite(&tuple_ty, &[result_value, overflow_value])
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
            UnOp::Not => Ok(self
                .value_encoder
                .wrap_bool(&self.value_is_true(&value).not())),
            UnOp::Neg => {
                let int_value = Int::from_i64(0) - self.value_int_data(&value);
                self.require_int_invariant(
                    state,
                    operand_ty,
                    &int_value,
                    span,
                    "type invariant does not hold".to_owned(),
                )?;
                Ok(self.value_encoder.wrap_int(&int_value))
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
                self.construct_composite(&spec_ty, &[])
            }
            TyKind::Adt(adt_def, _)
                if adt_def.is_struct() && adt_def.non_enum_variant().fields.is_empty() =>
            {
                let spec_ty = self.spec_ty_for_place_ty(ty, span)?;
                self.construct_composite(&spec_ty, &[])
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
                let ptr = self.mut_ptr(&value, inner_ty, span)?;
                self.construct_composite(spec_ty, &[current, fin, ptr])
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
                self.construct_composite(spec_ty, &items)
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
                self.construct_composite(spec_ty, &updated)
            }
            SpecTy::Struct(struct_ty) => {
                let mut updated = Vec::with_capacity(struct_ty.fields.len());
                for (index, field_ty) in struct_ty.fields.iter().enumerate() {
                    let field_value = self.project_field(value.clone(), spec_ty, index, span)?;
                    updated.push(self.dangle_value(&field_ty.ty, &field_value, span)?);
                }
                self.construct_composite(spec_ty, &updated)
            }
            SpecTy::Mut(inner) => {
                let fresh = self.fresh_for_spec_ty(inner, "dangle")?;
                let fin = self.mut_fin(value, inner, span)?;
                let ptr = self.mut_ptr(value, inner, span)?;
                self.construct_composite(spec_ty, &[fresh, fin, ptr])
            }
            SpecTy::Ref(_)
            | SpecTy::Seq(_)
            | SpecTy::Bool
            | SpecTy::RustTy
            | SpecTy::Int
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
            | SpecTy::Enum { .. }
            | SpecTy::Usize
            | SpecTy::TypeParam(_) => Ok(value.clone()),
        }
    }

    fn spec_expr_to_bool(
        &self,
        state: &State,
        expr: &TypedExpr,
        resolved: &ResolvedExprEnv,
    ) -> Result<Bool, VerificationResult> {
        match &expr.kind {
            TypedExprKind::Bool(value) => Ok(Bool::from_bool(*value)),
            TypedExprKind::Unary {
                op: UnaryOp::Not,
                arg,
            } => Ok(self.spec_expr_to_bool(state, arg, resolved)?.not()),
            TypedExprKind::Binary { op, lhs, rhs } => match op {
                BinaryOp::And => {
                    let lhs = self.spec_expr_to_bool(state, lhs, resolved)?;
                    let rhs = self.spec_expr_to_bool(state, rhs, resolved)?;
                    Ok(Bool::and(&[&lhs, &rhs]))
                }
                BinaryOp::Or => {
                    let lhs = self.spec_expr_to_bool(state, lhs, resolved)?;
                    let rhs = self.spec_expr_to_bool(state, rhs, resolved)?;
                    Ok(Bool::or(&[&lhs, &rhs]))
                }
                BinaryOp::Eq => {
                    let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                    let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                    self.eq_for_spec_ty(
                        &lhs.ty,
                        &lhs_value,
                        &rhs_value,
                        self.control_span(state.ctrl),
                    )
                }
                BinaryOp::Ne => {
                    let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                    let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                    Ok(self
                        .eq_for_spec_ty(
                            &lhs.ty,
                            &lhs_value,
                            &rhs_value,
                            self.control_span(state.ctrl),
                        )?
                        .not())
                }
                BinaryOp::Lt => {
                    let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                    let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .lt(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Le => {
                    let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                    let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .le(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Gt => {
                    let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                    let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .gt(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Ge => {
                    let lhs_value = self.spec_expr_to_value(state, lhs, resolved)?;
                    let rhs_value = self.spec_expr_to_value(state, rhs, resolved)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .ge(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
                    let value = self.spec_expr_to_value(state, expr, resolved)?;
                    Ok(self.value_is_true(&value))
                }
                BinaryOp::Concat => Err(self.unsupported_result(
                    self.control_span(state.ctrl),
                    "sequence value used where `bool` was required".to_owned(),
                )),
            },
            TypedExprKind::Match { .. } => {
                Ok(self.value_is_true(&self.spec_expr_to_value(state, expr, resolved)?))
            }
            _ => Ok(self.value_is_true(&self.spec_expr_to_value(state, expr, resolved)?)),
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
            TypedExprKind::RustType(key) => Ok(self.rust_ty_value(key)),
            TypedExprKind::SeqLit(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.spec_expr_to_value(state, item, resolved)?);
                }
                Ok(self.seq_literal_value(&values))
            }
            TypedExprKind::StructLit { fields } => {
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    values.push(self.spec_expr_to_value(state, field, resolved)?);
                }
                self.construct_composite(&expr.ty, &values)
            }
            TypedExprKind::Var(name) => state.spec_env.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.control_span(state.ctrl),
                    format!("missing spec binding `{name}`"),
                )
            }),
            TypedExprKind::RustVar(name) => {
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
            TypedExprKind::Match { .. } => Err(self.unsupported_result(
                self.control_span(state.ctrl),
                "match expressions are only supported in pure function bodies".to_owned(),
            )),
            TypedExprKind::PureCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.spec_expr_to_value(state, arg, resolved)?);
                }
                self.eval_pure_call(func, values, self.control_span(state.ctrl))
            }
            TypedExprKind::CtorCall {
                ctor_index, args, ..
            } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.spec_expr_to_value(state, arg, resolved)?);
                }
                self.construct_composite_ctor(&expr.ty, *ctor_index, &values)
            }
            TypedExprKind::Field { base, index, .. } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                self.project_field(value, &base.ty, *index, self.control_span(state.ctrl))
            }
            TypedExprKind::TupleField { base, index } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                self.project_field(value, &base.ty, *index, self.control_span(state.ctrl))
            }
            TypedExprKind::Index { base, index } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                let index_value = self.spec_expr_to_value(state, index, resolved)?;
                let index_int =
                    self.nat_to_int_term(&index_value, self.control_span(state.ctrl))?;
                self.seq_nth_value(&value, &index_int, self.control_span(state.ctrl))
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
    ) -> Result<Bool, VerificationResult> {
        match &expr.kind {
            TypedExprKind::Bool(value) => Ok(Bool::from_bool(*value)),
            TypedExprKind::Unary {
                op: UnaryOp::Not,
                arg,
            } => Ok(self.contract_expr_to_bool(current, spec, arg)?.not()),
            TypedExprKind::Binary { op, lhs, rhs } => match op {
                BinaryOp::And => {
                    let lhs = self.contract_expr_to_bool(current, spec, lhs)?;
                    let rhs = self.contract_expr_to_bool(current, spec, rhs)?;
                    Ok(Bool::and(&[&lhs, &rhs]))
                }
                BinaryOp::Or => {
                    let lhs = self.contract_expr_to_bool(current, spec, lhs)?;
                    let rhs = self.contract_expr_to_bool(current, spec, rhs)?;
                    Ok(Bool::or(&[&lhs, &rhs]))
                }
                BinaryOp::Eq => {
                    let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                    let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                    self.eq_for_spec_ty(&lhs.ty, &lhs_value, &rhs_value, self.report_span())
                }
                BinaryOp::Ne => {
                    let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                    let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                    Ok(self
                        .eq_for_spec_ty(&lhs.ty, &lhs_value, &rhs_value, self.report_span())?
                        .not())
                }
                BinaryOp::Lt => {
                    let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                    let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .lt(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Le => {
                    let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                    let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .le(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Gt => {
                    let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                    let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .gt(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Ge => {
                    let lhs_value = self.contract_expr_to_value(current, spec, lhs)?;
                    let rhs_value = self.contract_expr_to_value(current, spec, rhs)?;
                    Ok(self
                        .value_int_data(&lhs_value)
                        .ge(self.value_int_data(&rhs_value)))
                }
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
                    let value = self.contract_expr_to_value(current, spec, expr)?;
                    Ok(self.value_is_true(&value))
                }
                BinaryOp::Concat => Err(self.unsupported_result(
                    self.report_span(),
                    "sequence value used where `bool` was required".to_owned(),
                )),
            },
            TypedExprKind::Match { .. } => {
                Ok(self.value_is_true(&self.contract_expr_to_value(current, spec, expr)?))
            }
            _ => Ok(self.value_is_true(&self.contract_expr_to_value(current, spec, expr)?)),
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
            TypedExprKind::RustType(key) => Ok(self.rust_ty_value(key)),
            TypedExprKind::SeqLit(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.contract_expr_to_value(current, spec, item)?);
                }
                Ok(self.seq_literal_value(&values))
            }
            TypedExprKind::StructLit { fields } => {
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    values.push(self.contract_expr_to_value(current, spec, field)?);
                }
                self.construct_composite(&expr.ty, &values)
            }
            TypedExprKind::Var(name) => {
                if let Some(value) = spec.get(name).cloned() {
                    return Ok(value);
                }
                current.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.report_span(),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            TypedExprKind::RustVar(name) => current.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.report_span(),
                    format!("missing Rust binding `{name}`"),
                )
            }),
            TypedExprKind::Match {
                scrutinee,
                arms,
                default,
            } => self.contract_match_to_value(current, spec, scrutinee, arms, default.as_deref()),
            TypedExprKind::PureCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.contract_expr_to_value(current, spec, arg)?);
                }
                self.eval_pure_call(func, values, self.report_span())
            }
            TypedExprKind::CtorCall {
                ctor_index, args, ..
            } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.contract_expr_to_value(current, spec, arg)?);
                }
                self.construct_composite_ctor(&expr.ty, *ctor_index, &values)
            }
            TypedExprKind::Field { base, index, .. } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                self.project_field(value, &base.ty, *index, self.report_span())
            }
            TypedExprKind::TupleField { base, index } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                self.project_field(value, &base.ty, *index, self.report_span())
            }
            TypedExprKind::Index { base, index } => {
                let value = self.contract_expr_to_value(current, spec, base)?;
                let index_value = self.contract_expr_to_value(current, spec, index)?;
                let index_int = self.nat_to_int_term(&index_value, self.report_span())?;
                self.seq_nth_value(&value, &index_int, self.report_span())
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

    fn contract_match_to_value(
        &self,
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
        scrutinee: &TypedExpr,
        arms: &[crate::spec::TypedMatchArm],
        default: Option<&TypedExpr>,
    ) -> Result<SymValue, VerificationResult> {
        let scrutinee_value = self.contract_expr_to_value(current, spec, scrutinee)?;
        let composite = self.composite_encoding(&scrutinee.ty)?;
        let mut branches = Vec::with_capacity(arms.len());
        for arm in arms {
            let mut arm_current = current.clone();
            for (field_index, binding) in arm.bindings.iter().enumerate() {
                if let TypedMatchBinding::Var { name, .. } = binding {
                    let field_value = self
                        .value_encoder
                        .project_composite_ctor_field(
                            &composite,
                            arm.ctor_index,
                            &scrutinee_value,
                            field_index,
                        )
                        .map_err(|err| self.unsupported_result(self.report_span(), err))?;
                    arm_current.insert(name.clone(), field_value);
                }
            }
            let body = self.contract_expr_to_value(&arm_current, spec, &arm.body)?;
            let guard = self.composite_tag_formula_for_encoding(
                &composite,
                &scrutinee_value,
                arm.ctor_index,
                self.report_span(),
            )?;
            branches.push((guard, body));
        }
        let mut result = if let Some(default) = default {
            self.contract_expr_to_value(current, spec, default)?
        } else {
            branches
                .last()
                .map(|(_, value)| value.clone())
                .ok_or_else(|| {
                    self.unsupported_result(
                        self.report_span(),
                        "match expression must contain at least one arm".to_owned(),
                    )
                })?
        };
        for (guard, value) in branches.into_iter().rev() {
            result = SymValue::new(guard.ite(value.dynamic(), result.dynamic()));
        }
        Ok(result)
    }

    fn eval_pure_call(
        &self,
        func: &str,
        values: Vec<SymValue>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        if let Some(value) = self.eval_builtin_pure_call(func, &values, span)? {
            return Ok(value);
        }
        if let Some(value) = self.try_eval_ground_pure_call(func, &values, span)? {
            return Ok(value);
        }
        let Some(decl) = self.pure_fn_decls.get(func) else {
            return Err(self.unsupported_result(span, format!("unknown pure function `{func}`")));
        };
        let args: Vec<&dyn Ast> = values.iter().map(SymValue::ast).collect();
        Ok(SymValue::new(decl.apply(&args)))
    }

    fn try_eval_ground_pure_call(
        &self,
        func: &str,
        values: &[SymValue],
        span: Span,
    ) -> Result<Option<SymValue>, VerificationResult> {
        if let Some(value) = self.eval_builtin_pure_call(func, values, span)? {
            return Ok(Some(value));
        }
        let Some(pure_fn) = self.pure_fns.get(func) else {
            return Ok(None);
        };
        if pure_fn.params.len() != values.len() {
            return Ok(None);
        }
        let mut env = HashMap::new();
        for (param, value) in pure_fn.params.iter().zip(values.iter()) {
            env.insert(param.name.clone(), value.clone());
        }
        self.try_eval_ground_pure_expr(&pure_fn.body, &env, span)
    }

    fn eval_builtin_pure_call(
        &self,
        func: &str,
        values: &[SymValue],
        span: Span,
    ) -> Result<Option<SymValue>, VerificationResult> {
        match (func, values) {
            ("seq_len", [value]) => {
                let length = self.seq_len_int(value, span)?;
                if let Some(length) = length.simplify().as_i64()
                    && length >= 0
                {
                    return Ok(Some(self.concrete_nat_value(length as u64)?));
                }
                Ok(Some(self.int_to_nat_value(&length, span)?))
            }
            ("seq_len", _) => Err(self.unsupported_result(
                span,
                format!("builtin pure function `{func}` expects 1 argument"),
            )),
            _ => Ok(None),
        }
    }

    fn try_eval_ground_pure_expr(
        &self,
        expr: &TypedExpr,
        env: &HashMap<String, SymValue>,
        span: Span,
    ) -> Result<Option<SymValue>, VerificationResult> {
        Ok(match &expr.kind {
            TypedExprKind::Bool(value) => Some(self.value_bool(*value)),
            TypedExprKind::Int(value) => Some(self.value_decimal_int(&value.digits, span)?),
            TypedExprKind::RustType(key) => Some(self.rust_ty_value(key)),
            TypedExprKind::SeqLit(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    let Some(value) = self.try_eval_ground_pure_expr(item, env, span)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                Some(self.seq_literal_value(&values))
            }
            TypedExprKind::StructLit { fields } => {
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    let Some(value) = self.try_eval_ground_pure_expr(field, env, span)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                Some(self.construct_composite(&expr.ty, &values)?)
            }
            TypedExprKind::Var(name) | TypedExprKind::RustVar(name) => env.get(name).cloned(),
            TypedExprKind::CtorCall {
                ctor_index, args, ..
            } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    let Some(value) = self.try_eval_ground_pure_expr(arg, env, span)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                Some(self.construct_composite_ctor(&expr.ty, *ctor_index, &values)?)
            }
            TypedExprKind::PureCall { func, args } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    let Some(value) = self.try_eval_ground_pure_expr(arg, env, span)? else {
                        return Ok(None);
                    };
                    values.push(value);
                }
                if let Some(value) = self.try_eval_ground_pure_call(func, &values, span)? {
                    Some(value)
                } else {
                    let Some(decl) = self.pure_fn_decls.get(func) else {
                        return Err(self
                            .unsupported_result(span, format!("unknown pure function `{func}`")));
                    };
                    let args: Vec<&dyn Ast> = values.iter().map(SymValue::ast).collect();
                    Some(SymValue::new(decl.apply(&args)))
                }
            }
            TypedExprKind::Match {
                scrutinee,
                arms,
                default,
            } => {
                let Some(scrutinee_value) = self.try_eval_ground_pure_expr(scrutinee, env, span)?
                else {
                    return Ok(None);
                };
                let Some(ctor_index) =
                    self.ground_ctor_index(&scrutinee.ty, &scrutinee_value, span)?
                else {
                    return Ok(None);
                };
                if let Some(arm) = arms.iter().find(|arm| arm.ctor_index == ctor_index) {
                    let composite = self.composite_encoding(&scrutinee.ty)?;
                    let mut arm_env = env.clone();
                    for (field_index, binding) in arm.bindings.iter().enumerate() {
                        if let TypedMatchBinding::Var { name, .. } = binding {
                            let field_value = self
                                .value_encoder
                                .project_composite_ctor_field(
                                    &composite,
                                    ctor_index,
                                    &scrutinee_value,
                                    field_index,
                                )
                                .map_err(|err| self.unsupported_result(span, err))?;
                            arm_env.insert(name.clone(), field_value);
                        }
                    }
                    self.try_eval_ground_pure_expr(&arm.body, &arm_env, span)?
                } else if let Some(default) = default {
                    self.try_eval_ground_pure_expr(default, env, span)?
                } else {
                    return Ok(None);
                }
            }
            TypedExprKind::Field { base, index, .. } => {
                let Some(value) = self.try_eval_ground_pure_expr(base, env, span)? else {
                    return Ok(None);
                };
                Some(self.project_field(value, &base.ty, *index, span)?)
            }
            TypedExprKind::TupleField { base, index } => {
                let Some(value) = self.try_eval_ground_pure_expr(base, env, span)? else {
                    return Ok(None);
                };
                Some(self.project_field(value, &base.ty, *index, span)?)
            }
            TypedExprKind::Index { base, index } => {
                let Some(value) = self.try_eval_ground_pure_expr(base, env, span)? else {
                    return Ok(None);
                };
                let Some(index_value) = self.try_eval_ground_pure_expr(index, env, span)? else {
                    return Ok(None);
                };
                let index_int = self.nat_to_int_term(&index_value, span)?;
                Some(self.seq_nth_value(&value, &index_int, span)?)
            }
            TypedExprKind::Unary { op, arg } => {
                let Some(value) = self.try_eval_ground_pure_expr(arg, env, span)? else {
                    return Ok(None);
                };
                Some(self.lower_unary_value(*op, &value))
            }
            TypedExprKind::Binary { op, lhs, rhs } => {
                let Some(lhs_value) = self.try_eval_ground_pure_expr(lhs, env, span)? else {
                    return Ok(None);
                };
                let Some(rhs_value) = self.try_eval_ground_pure_expr(rhs, env, span)? else {
                    return Ok(None);
                };
                Some(self.lower_binary_value(*op, &lhs.ty, &lhs_value, &rhs_value, span)?)
            }
        })
    }

    fn ground_ctor_index(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<usize>, VerificationResult> {
        let composite = self.composite_encoding(ty)?;
        let decl_name = value.dynamic().decl().name();
        for (ctor_index, ctor) in composite.constructors.iter().enumerate() {
            if decl_name == ctor.symbol.name() {
                return Ok(Some(ctor_index));
            }
        }
        let _ = span;
        Ok(None)
    }

    fn assert_constraint(
        &self,
        state: &mut State,
        constraint: Bool,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<(), VerificationResult> {
        let constraint = constraint.simplify();
        if let Some(value) = constraint.as_bool() {
            return match value {
                true => {
                    self.add_path_condition(state, constraint);
                    Ok(())
                }
                false => Err(VerificationResult {
                    function: self.report_function(),
                    status: VerificationStatus::Fail,
                    span: diagnostic_span,
                    message,
                }),
            };
        }
        match self.check_sat(&[state.pc.clone(), constraint.not()]) {
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
            SatResult::Unknown => Err(self.unknown_solver_result(span, "checking an assertion")),
        }
    }

    fn bind_state_spec_values(
        &self,
        state: &mut State,
        bindings: &[NormalizedBinding],
        resolved: &ResolvedExprEnv,
    ) -> Result<(), VerificationResult> {
        for binding in bindings {
            let value = self.spec_expr_to_value(state, &binding.value, resolved)?;
            state.spec_env.insert(binding.name.clone(), value);
        }
        Ok(())
    }

    fn bind_contract_spec_values(
        &self,
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
        bindings: &[NormalizedBinding],
    ) -> Result<HashMap<String, SymValue>, VerificationResult> {
        let mut bound = spec.clone();
        for binding in bindings {
            let value = self.contract_expr_to_value(current, &bound, &binding.value)?;
            bound.insert(binding.name.clone(), value);
        }
        Ok(bound)
    }

    fn assert_predicate_constraint(
        &self,
        state: &mut State,
        constraint: Bool,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<(), VerificationResult> {
        self.assert_constraint(state, constraint, span, diagnostic_span, message)
    }

    fn assert_spec_predicate_constraint(
        &self,
        state: &mut State,
        predicate: &NormalizedPredicate,
        resolved: &ResolvedExprEnv,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<(), VerificationResult> {
        self.bind_state_spec_values(state, &predicate.bindings, resolved)?;
        let constraint = self.spec_expr_to_bool(state, &predicate.condition, resolved)?;
        self.assert_predicate_constraint(state, constraint, span, diagnostic_span, message)
    }

    fn assert_contract_predicate_constraint(
        &self,
        state: &mut State,
        predicate: &NormalizedPredicate,
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
        span: Span,
        diagnostic_span: String,
        message: String,
    ) -> Result<HashMap<String, SymValue>, VerificationResult> {
        let spec = self.bind_contract_spec_values(current, spec, &predicate.bindings)?;
        let constraint = self.contract_expr_to_bool(current, &spec, &predicate.condition)?;
        self.assert_predicate_constraint(state, constraint, span, diagnostic_span, message)?;
        Ok(spec)
    }

    fn assume_contract_predicate(
        &self,
        state: &mut State,
        predicate: &NormalizedPredicate,
        current: &HashMap<String, SymValue>,
        spec: &HashMap<String, SymValue>,
    ) -> Result<Option<HashMap<String, SymValue>>, VerificationResult> {
        let spec = self.bind_contract_spec_values(current, spec, &predicate.bindings)?;
        let constraint = self.contract_expr_to_bool(current, &spec, &predicate.condition)?;
        if self.assume_path_condition(state, constraint) {
            Ok(Some(spec))
        } else {
            Ok(None)
        }
    }

    // Assumptions only strengthen the current path condition; asking Z3 whether they
    // are satisfiable is optional and was the main source of spurious `unknown`s
    // once recursive prelude definitions were loaded.
    fn assume_path_condition(&self, state: &mut State, constraint: Bool) -> bool {
        let constraint = constraint.simplify();
        match constraint.as_bool() {
            Some(true) => {
                self.add_path_condition(state, constraint);
                true
            }
            Some(false) => false,
            None => {
                self.add_path_condition(state, constraint);
                true
            }
        }
    }

    fn assume_checked_path_condition(&self, state: &mut State, constraint: Bool) -> bool {
        let constraint = constraint.simplify();
        if let Some(value) = constraint.as_bool() {
            if value {
                self.add_path_condition(state, constraint);
                return true;
            }
            return false;
        }
        match self.check_sat(&[state.pc.clone(), constraint.clone()]) {
            SatResult::Sat => {
                self.add_path_condition(state, constraint);
                true
            }
            SatResult::Unsat => false,
            SatResult::Unknown => {
                self.add_path_condition(state, constraint);
                true
            }
        }
    }

    fn unknown_solver_result(&self, span: Span, context: &str) -> VerificationResult {
        VerificationResult {
            function: self.report_function(),
            status: VerificationStatus::Fail,
            span: if span == DUMMY_SP {
                "no-location".to_owned()
            } else {
                self.tcx.sess.source_map().span_to_diagnostic_string(span)
            },
            message: format!("solver returned unknown while {context}"),
        }
    }

    fn timeout_solver_result(&self, span: Span, context: &str) -> VerificationResult {
        VerificationResult {
            function: self.report_function(),
            status: VerificationStatus::Fail,
            span: if span == DUMMY_SP {
                "no-location".to_owned()
            } else {
                self.tcx.sess.source_map().span_to_diagnostic_string(span)
            },
            message: format!("solver timed out while {context}"),
        }
    }

    fn prune_state(
        &self,
        mut state: State,
        constraint: Bool,
        _span: Span,
    ) -> Result<Option<State>, VerificationResult> {
        let constraint = constraint.simplify();
        if let Some(value) = constraint.as_bool() {
            if value {
                self.add_path_condition(&mut state, constraint);
                return Ok(Some(state));
            }
            return Ok(None);
        }
        match self.check_sat(&[state.pc.clone(), constraint.clone()]) {
            SatResult::Sat => {
                self.add_path_condition(&mut state, constraint);
                Ok(Some(state))
            }
            SatResult::Unsat => Ok(None),
            SatResult::Unknown => {
                self.add_path_condition(&mut state, constraint);
                Ok(Some(state))
            }
        }
    }

    fn prune_unsafe_state(
        &self,
        mut state: UnsafeState,
        constraint: Bool,
        _span: Span,
    ) -> Result<Option<UnsafeState>, VerificationResult> {
        let constraint = constraint.simplify();
        if let Some(value) = constraint.as_bool() {
            if value {
                self.add_unsafe_path_condition(&mut state, constraint);
                return Ok(Some(state));
            }
            return Ok(None);
        }
        match self.check_sat(&[state.pc.clone(), constraint.clone()]) {
            SatResult::Sat => {
                self.add_unsafe_path_condition(&mut state, constraint);
                Ok(Some(state))
            }
            SatResult::Unsat => Ok(None),
            SatResult::Unknown => {
                self.add_unsafe_path_condition(&mut state, constraint);
                Ok(Some(state))
            }
        }
    }

    fn add_path_condition(&self, state: &mut State, constraint: Bool) {
        state.pc = bool_and(vec![state.pc.clone(), constraint]).simplify();
    }

    fn check_sat(&self, assumptions: &[Bool]) -> SatResult {
        let assumptions = assumptions.iter().map(Bool::simplify).collect::<Vec<_>>();
        with_solver(|solver| solver.check_assumptions(&assumptions))
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
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let inner_spec_ty = self.spec_ty_for_place_ty(inner_ty, self.report_span())?;
        let final_value = self.mut_fin(value, &inner_spec_ty, self.report_span())?;
        let fresh = self.fresh_for_rust_ty(inner_ty, "opaque_cur")?;
        let ptr = self.mut_ptr(value, &inner_spec_ty, span)?;
        self.construct_composite(
            &SpecTy::Mut(Box::new(inner_spec_ty)),
            &[fresh, final_value, ptr],
        )
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

    fn called_local_def_id(&self, func: &Operand<'tcx>) -> Option<LocalDefId> {
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

    fn unsafe_block_containing_span(&self, span: Span) -> Option<Span> {
        self.function_context()
            .unsafe_blocks
            .iter()
            .copied()
            .find(|unsafe_span| span_contains(*unsafe_span, span))
    }

    fn value_int(&self, value: i64) -> SymValue {
        self.value_encoder.int_value(value)
    }

    fn value_decimal_int(&self, digits: &str, span: Span) -> Result<SymValue, VerificationResult> {
        self.value_encoder.decimal_int_value(digits).map_err(|_| {
            self.unsupported_result(span, format!("invalid integer literal `{digits}`"))
        })
    }

    fn value_bool(&self, value: bool) -> SymValue {
        self.value_encoder.bool_value(value)
    }

    fn rust_ty_value(&self, key: &RustTyKey) -> SymValue {
        with_solver(|solver| self.value_encoder.rust_ty_value(key, solver))
    }

    fn value_is_true(&self, value: &SymValue) -> Bool {
        self.value_encoder.bool_term(value)
    }

    fn value_int_data(&self, value: &SymValue) -> Int {
        self.value_encoder.int_term(value)
    }

    fn seq_literal_value(&self, items: &[SymValue]) -> SymValue {
        self.value_encoder.seq_literal_value(items)
    }

    fn seq_len_int(&self, value: &SymValue, span: Span) -> Result<Int, VerificationResult> {
        self.value_encoder
            .seq_len_int(value)
            .map_err(|err| self.unsupported_result(span, err))
    }

    fn seq_nth_value(
        &self,
        value: &SymValue,
        index: &Int,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        self.value_encoder
            .seq_nth_value(value, index)
            .map_err(|err| self.unsupported_result(span, err))
    }

    fn eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        with_solver(|solver| self.value_encoder.eq_for_spec_ty(ty, lhs, rhs, solver))
            .map_err(|err| self.unsupported_result(span, err))
    }

    fn lower_unary_value(&self, op: UnaryOp, value: &SymValue) -> SymValue {
        self.value_encoder.lower_unary_value(op, value)
    }

    fn lower_binary_value(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        with_solver(|solver| {
            self.value_encoder
                .lower_binary_value(op, lhs_ty, lhs, rhs, solver)
        })
        .map_err(|err| self.unsupported_result(span, err))
    }

    fn type_encoding(&self, ty: &SpecTy) -> Result<Rc<TypeEncoding>, VerificationResult> {
        with_solver(|solver| self.value_encoder.type_encoding(ty, solver))
            .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn composite_encoding(&self, ty: &SpecTy) -> Result<Rc<CompositeEncoding>, VerificationResult> {
        with_solver(|solver| self.value_encoder.composite_encoding(ty, solver))
            .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn construct_composite(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
    ) -> Result<SymValue, VerificationResult> {
        with_solver(|solver| self.value_encoder.construct_composite(ty, fields, solver))
            .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn construct_composite_ctor(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
    ) -> Result<SymValue, VerificationResult> {
        with_solver(|solver| {
            self.value_encoder
                .construct_composite_ctor(ty, ctor_index, fields, solver)
        })
        .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn construct_composite_ctor_without_axioms(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
    ) -> Result<SymValue, VerificationResult> {
        self.value_encoder
            .construct_composite_ctor_without_axioms(ty, ctor_index, fields)
            .map_err(|err| self.unsupported_result(self.report_span(), err))
    }

    fn fresh_for_rust_ty(&self, ty: Ty<'tcx>, hint: &str) -> Result<SymValue, VerificationResult> {
        match ty.kind() {
            TyKind::RawPtr(pointee, _) => {
                return self.fresh_raw_ptr_for_pointee_ty(*pointee, hint);
            }
            TyKind::Ref(_, inner, mutability) => {
                let inner_spec_ty = spec_ty_for_rust_ty(self.tcx, *inner)
                    .map_err(|err| self.unsupported_result(self.report_span(), err))?;
                let ptr = self.fresh_ref_ptr_for_pointee_ty(*inner, hint)?;
                if mutability.is_mut() {
                    let current = self.fresh_for_rust_ty(*inner, &format!("{hint}_cur"))?;
                    let final_value = self.fresh_for_rust_ty(*inner, &format!("{hint}_fin"))?;
                    return self.construct_composite(
                        &SpecTy::Mut(Box::new(inner_spec_ty)),
                        &[current, final_value, ptr],
                    );
                }
                let value = self.fresh_for_rust_ty(*inner, &format!("{hint}_deref"))?;
                return self
                    .construct_composite(&SpecTy::Ref(Box::new(inner_spec_ty)), &[value, ptr]);
            }
            _ => {}
        }
        let spec_ty = spec_ty_for_rust_ty(self.tcx, ty)
            .map_err(|err| self.unsupported_result(self.report_span(), err))?;
        if let TyKind::Adt(adt_def, args) = ty.kind() {
            debug_assert!(adt_def.is_struct());
            let is_seq_model = matches!(spec_ty, SpecTy::Seq(_));
            if !args.is_empty() && !is_seq_model {
                return Err(self.unsupported_result(
                    self.report_span(),
                    format!("generic structs are unsupported: {ty:?}"),
                ));
            }
            if adt_def.has_dtor(self.tcx) && !is_seq_model {
                return Err(self.unsupported_result(
                    self.report_span(),
                    format!("structs with Drop are unsupported: {ty:?}"),
                ));
            }
        }
        self.fresh_for_spec_ty(&spec_ty, hint)
    }

    fn fresh_raw_ptr_for_pointee_ty(
        &self,
        pointee_ty: Ty<'tcx>,
        hint: &str,
    ) -> Result<SymValue, VerificationResult> {
        let addr = self.fresh_for_spec_ty(&SpecTy::Usize, &format!("{hint}_addr"))?;
        let prov = self.construct_option_none(provenance_spec_ty())?;
        let ty = self.rust_ty_model_value(pointee_ty);
        self.construct_composite(&ptr_spec_ty(), &[addr, prov, ty])
    }

    fn fresh_ref_ptr_for_pointee_ty(
        &self,
        pointee_ty: Ty<'tcx>,
        hint: &str,
    ) -> Result<SymValue, VerificationResult> {
        self.fresh_ref_ptr_with_ty_value(hint, self.rust_ty_model_value(pointee_ty))
    }

    fn fresh_ref_ptr_with_ty_value(
        &self,
        hint: &str,
        ty: SymValue,
    ) -> Result<SymValue, VerificationResult> {
        let addr = self.fresh_for_spec_ty(&SpecTy::Usize, &format!("{hint}_addr"))?;
        let provenance = self.construct_provenance(addr.clone())?;
        let prov = self.construct_option_some(provenance_spec_ty(), provenance)?;
        self.construct_composite(&ptr_spec_ty(), &[addr, prov, ty])
    }

    fn create_allocation(
        &self,
        state: &mut State,
        local: Local,
        hint: &str,
        span: Span,
    ) -> Result<(), VerificationResult> {
        state.allocs.remove(&local);
        let ty = self.body().local_decls[local].ty;
        let (size, align) = self.layout_size_align_bytes(ty, span)?;
        let base_addr =
            self.fresh_for_spec_ty(&SpecTy::Usize, &format!("{hint}_{}_base", local.as_usize()))?;
        let alloc = Allocation {
            base_addr,
            size,
            align,
        };

        self.add_path_condition(state, self.allocation_bounds_formula(&alloc, span)?);
        let other_allocs = state.allocs.values().cloned().collect::<Vec<_>>();
        for other in &other_allocs {
            self.add_path_condition(
                state,
                self.allocation_distinct_formula(&alloc, other, span)?,
            );
            if alloc.size != 0 && other.size != 0 {
                self.add_path_condition(
                    state,
                    self.allocation_non_overlapping_formula(&alloc, other),
                );
            }
        }
        state.allocs.insert(local, alloc);
        Ok(())
    }

    fn allocations_are_identical(&self, lhs: &Allocation, rhs: &Allocation) -> bool {
        lhs.size == rhs.size && lhs.align == rhs.align && lhs.base_addr == rhs.base_addr
    }

    fn allocation_equality_formula(
        &self,
        lhs: &Allocation,
        rhs: &Allocation,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        if lhs.size != rhs.size || lhs.align != rhs.align {
            return Ok(Bool::from_bool(false));
        }
        self.eq_for_spec_ty(&SpecTy::Usize, &lhs.base_addr, &rhs.base_addr, span)
    }

    fn allocation_distinct_formula(
        &self,
        lhs: &Allocation,
        rhs: &Allocation,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        Ok(self
            .eq_for_spec_ty(&SpecTy::Usize, &lhs.base_addr, &rhs.base_addr, span)?
            .not())
    }

    fn allocation_bounds_formula(
        &self,
        alloc: &Allocation,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let mut formulas = Vec::new();
        if let Some(base_in_range) = self.spec_ty_formula(&SpecTy::Usize, &alloc.base_addr, span)? {
            formulas.push(base_in_range);
        }
        let (_, usize_max) = self.pointer_sized_int_bounds(false)?;
        let end = self.value_int_data(&alloc.base_addr) + Int::from_u64(alloc.size);
        formulas.push(end.le(usize_max));
        if alloc.align > 1 {
            let base = self.value_int_data(&alloc.base_addr);
            formulas.push(base.modulo(Int::from_u64(alloc.align)).eq(0));
        }
        Ok(bool_and(formulas))
    }

    fn allocation_non_overlapping_formula(&self, alloc: &Allocation, other: &Allocation) -> Bool {
        let alloc_base = self.value_int_data(&alloc.base_addr);
        let alloc_end = alloc_base.clone() + Int::from_u64(alloc.size);
        let other_base = self.value_int_data(&other.base_addr);
        let other_end = other_base.clone() + Int::from_u64(other.size);
        Bool::or(&[&alloc_end.le(&other_base), &other_end.le(alloc_base)])
    }

    fn ptr_for_place(
        &self,
        state: &State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let projection = place.as_ref().projection;
        let final_ty = self.place_ty(place);
        if matches!(projection.first(), Some(PlaceElem::Deref)) {
            let Some(root) = state.model.get(&place.local).cloned() else {
                return Err(self.unsupported_result(
                    span,
                    format!("missing local {}", place.local.as_usize()),
                ));
            };
            let root_ty = self.body().local_decls[place.local].ty;
            let root_spec_ty = self.spec_ty_for_place_ty(root_ty, span)?;
            let base_ptr = self.ptr_for_deref_base(&root, &root_spec_ty, span)?;
            let pointee_ty = self.deref_pointee_ty(root_ty, span)?;
            return self.ptr_for_base_projection(
                &base_ptr,
                pointee_ty,
                &projection[1..],
                final_ty,
                span,
            );
        }

        let alloc = state.allocs.get(&place.local).ok_or_else(|| {
            self.unsupported_result(
                span,
                format!("missing allocation for local {}", place.local.as_usize()),
            )
        })?;
        let root_ty = self.body().local_decls[place.local].ty;
        let offset = self.place_projection_offset(root_ty, projection, span)?;
        let addr = self.add_addr_offset(alloc.base_addr.clone(), offset);
        let provenance = self.construct_provenance(alloc.base_addr.clone())?;
        let prov = self.construct_option_some(provenance_spec_ty(), provenance)?;
        let ty = self.rust_ty_model_value(final_ty);
        self.construct_ptr(addr, prov, ty)
    }

    fn ptr_for_deref_base(
        &self,
        value: &SymValue,
        spec_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        match spec_ty {
            SpecTy::Ref(inner) => self.ref_ptr(value, inner, span),
            SpecTy::Mut(inner) => self.mut_ptr(value, inner, span),
            SpecTy::Struct(struct_ty) if struct_ty.name == "Ptr" => Ok(value.clone()),
            _ => Err(self.unsupported_result(
                span,
                format!("raw pointer requested through non-pointer place `{spec_ty:?}`"),
            )),
        }
    }

    fn ptr_for_base_projection(
        &self,
        base_ptr: &SymValue,
        base_ty: Ty<'tcx>,
        projection: &[PlaceElem<'tcx>],
        final_ty: Ty<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let offset = self.place_projection_offset(base_ty, projection, span)?;
        let addr = self.add_addr_offset(self.ptr_addr(base_ptr, span)?, offset);
        let prov = self.ptr_prov(base_ptr, span)?;
        let ty = self.rust_ty_model_value(final_ty);
        self.construct_ptr(addr, prov, ty)
    }

    fn deref_pointee_ty(&self, ty: Ty<'tcx>, span: Span) -> Result<Ty<'tcx>, VerificationResult> {
        match ty.kind() {
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => Ok(*inner),
            other => Err(self.unsupported_result(
                span,
                format!("raw pointer requested through non-pointer type `{other:?}`"),
            )),
        }
    }

    fn place_projection_offset(
        &self,
        root_ty: Ty<'tcx>,
        projection: &[PlaceElem<'tcx>],
        span: Span,
    ) -> Result<u64, VerificationResult> {
        let mut ty = root_ty;
        let mut offset = 0;
        for elem in projection {
            match elem {
                PlaceElem::Field(field, field_ty) => {
                    let layout = self.layout_for_ty(ty, span)?;
                    offset += layout.layout.fields().offset(field.index()).bytes();
                    ty = *field_ty;
                }
                other => {
                    return Err(self.unsupported_result(
                        span,
                        format!("unsupported layout-dependent place projection {other:?}"),
                    ));
                }
            }
        }
        Ok(offset)
    }

    fn add_addr_offset(&self, base: SymValue, offset: u64) -> SymValue {
        if offset == 0 {
            return base;
        }
        self.value_encoder
            .wrap_int(&(self.value_int_data(&base) + Int::from_u64(offset)))
    }

    fn layout_for_ty(
        &self,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<TyAndLayout<'tcx>, VerificationResult> {
        self.tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
            .map_err(|err| {
                self.unsupported_result(span, format!("unsupported layout for `{ty}`: {err:?}"))
            })
    }

    fn layout_size_align_bytes(
        &self,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Result<(u64, u64), VerificationResult> {
        match self.layout_for_ty(ty, span) {
            Ok(layout) => Ok((
                layout.layout.size().bytes(),
                layout.layout.align().abi.bytes(),
            )),
            Err(err) if matches!(ty.kind(), TyKind::RawPtr(_, _) | TyKind::Ref(_, _, _)) => {
                let _ = err;
                Ok((
                    self.tcx.data_layout.pointer_size().bytes(),
                    self.tcx.data_layout.pointer_align().abi.bytes(),
                ))
            }
            Err(err) => Err(err),
        }
    }

    fn ptr_without_provenance(
        &self,
        pointee_ty: Ty<'tcx>,
        addr: SymValue,
    ) -> Result<SymValue, VerificationResult> {
        let prov = self.construct_option_none(provenance_spec_ty())?;
        let ty = self.rust_ty_model_value(pointee_ty);
        self.construct_ptr(addr, prov, ty)
    }

    fn construct_ptr(
        &self,
        addr: SymValue,
        prov: SymValue,
        ty: SymValue,
    ) -> Result<SymValue, VerificationResult> {
        self.construct_composite(&ptr_spec_ty(), &[addr, prov, ty])
    }

    fn construct_provenance(&self, base: SymValue) -> Result<SymValue, VerificationResult> {
        self.construct_composite(&provenance_spec_ty(), &[base])
    }

    fn construct_option_none(&self, inner: SpecTy) -> Result<SymValue, VerificationResult> {
        let ctor_index = self
            .value_encoder
            .enum_ctor_index("Option", "None")
            .map_err(|err| self.unsupported_result(self.report_span(), err))?;
        self.construct_composite_ctor_without_axioms(&option_spec_ty(inner), ctor_index, &[])
    }

    fn construct_option_some(
        &self,
        inner: SpecTy,
        value: SymValue,
    ) -> Result<SymValue, VerificationResult> {
        let ctor_index = self
            .value_encoder
            .enum_ctor_index("Option", "Some")
            .map_err(|err| self.unsupported_result(self.report_span(), err))?;
        self.construct_composite_ctor_without_axioms(&option_spec_ty(inner), ctor_index, &[value])
    }

    fn rust_ty_model_value(&self, ty: Ty<'tcx>) -> SymValue {
        self.rust_ty_value(&self.rust_ty_key_for_rust_ty(ty))
    }

    fn local_rust_ty_model_value(&self, local: Local) -> SymValue {
        self.rust_ty_model_value(self.body().local_decls[local].ty)
    }

    fn rust_ty_key_for_rust_ty(&self, ty: Ty<'tcx>) -> RustTyKey {
        RustTyKey::new(self.rust_ty_key_text_for_rust_ty(ty))
    }

    fn rust_ty_key_text_for_rust_ty(&self, ty: Ty<'tcx>) -> String {
        match ty.kind() {
            TyKind::Bool => "bool".to_owned(),
            TyKind::Int(kind) => match kind {
                ty::IntTy::I8 => "i8".to_owned(),
                ty::IntTy::I16 => "i16".to_owned(),
                ty::IntTy::I32 => "i32".to_owned(),
                ty::IntTy::I64 => "i64".to_owned(),
                ty::IntTy::I128 => "i128".to_owned(),
                ty::IntTy::Isize => "isize".to_owned(),
            },
            TyKind::Uint(kind) => match kind {
                ty::UintTy::U8 => "u8".to_owned(),
                ty::UintTy::U16 => "u16".to_owned(),
                ty::UintTy::U32 => "u32".to_owned(),
                ty::UintTy::U64 => "u64".to_owned(),
                ty::UintTy::U128 => "u128".to_owned(),
                ty::UintTy::Usize => "usize".to_owned(),
            },
            TyKind::RawPtr(pointee, mutability) => {
                let kind = if mutability.is_mut() { "mut" } else { "const" };
                format!("*{kind} {}", self.rust_ty_key_text_for_rust_ty(*pointee))
            }
            TyKind::Ref(_, inner, mutability) => {
                let inner = self.rust_ty_key_text_for_rust_ty(*inner);
                if mutability.is_mut() {
                    format!("&mut {inner}")
                } else {
                    format!("&{inner}")
                }
            }
            TyKind::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| self.rust_ty_key_text_for_rust_ty(field))
                    .collect::<Vec<_>>();
                match fields.as_slice() {
                    [] => "()".to_owned(),
                    [field] => format!("({field},)"),
                    _ => format!("({})", fields.join(", ")),
                }
            }
            TyKind::Adt(adt_def, args) => {
                let mut text = self.tcx.def_path_str(adt_def.did());
                let type_args = args
                    .types()
                    .map(|arg| self.rust_ty_key_text_for_rust_ty(arg))
                    .collect::<Vec<_>>();
                if !type_args.is_empty() {
                    text.push('<');
                    text.push_str(&type_args.join(", "));
                    text.push('>');
                }
                text
            }
            TyKind::Param(param) => param.name.to_string(),
            _ => format!("{ty:?}"),
        }
    }

    fn fresh_for_spec_ty(&self, ty: &SpecTy, hint: &str) -> Result<SymValue, VerificationResult> {
        match ty {
            SpecTy::Ref(inner) => {
                let deref = self.fresh_for_spec_ty(inner, &format!("{hint}_deref"))?;
                let ptr_ty = self.fresh_for_spec_ty(&SpecTy::RustTy, &format!("{hint}_ptr_ty"))?;
                let ptr = self.fresh_ref_ptr_with_ty_value(hint, ptr_ty)?;
                return self.construct_composite(ty, &[deref, ptr]);
            }
            SpecTy::Mut(inner) => {
                let current = self.fresh_for_spec_ty(inner, &format!("{hint}_cur"))?;
                let final_value = self.fresh_for_spec_ty(inner, &format!("{hint}_fin"))?;
                let ptr_ty = self.fresh_for_spec_ty(&SpecTy::RustTy, &format!("{hint}_ptr_ty"))?;
                let ptr = self.fresh_ref_ptr_with_ty_value(hint, ptr_ty)?;
                return self.construct_composite(ty, &[current, final_value, ptr]);
            }
            _ => {}
        }
        if matches!(ty, SpecTy::Enum { .. }) {
            return Ok(SymValue::new(Dynamic::new_const(
                self.fresh_name(hint),
                self.value_encoder.value_sort(),
            )));
        }
        let encoding = self.type_encoding(ty)?;
        self.fresh_for_encoding(&encoding, hint)
    }

    fn fresh_for_encoding(
        &self,
        encoding: &TypeEncoding,
        hint: &str,
    ) -> Result<SymValue, VerificationResult> {
        match &encoding.kind {
            TypeEncodingKind::Bool => Ok(self
                .value_encoder
                .wrap_bool(&Bool::new_const(self.fresh_name(hint)))),
            TypeEncodingKind::Int => Ok(self
                .value_encoder
                .wrap_int(&Int::new_const(self.fresh_name(hint)))),
            TypeEncodingKind::Opaque => Ok(SymValue::new(Dynamic::new_const(
                self.fresh_name(hint),
                self.value_encoder.value_sort(),
            ))),
            TypeEncodingKind::Seq => Ok(SymValue::new(Dynamic::from(Z3Seq::new_const(
                self.fresh_name(hint),
                self.value_encoder.value_sort(),
            )))),
            TypeEncodingKind::Composite(composite) => {
                let ctor = composite
                    .single_constructor()
                    .map_err(|err| self.unsupported_result(self.report_span(), err))?;
                let mut fields = Vec::with_capacity(ctor.fields.len());
                for (index, field) in ctor.fields.iter().enumerate() {
                    fields.push(self.fresh_for_spec_ty(&field.ty, &format!("{hint}_{index}"))?);
                }
                let args = fields.iter().map(SymValue::ast).collect::<Vec<_>>();
                Ok(SymValue::new(ctor.symbol.apply(&args)))
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
        with_solver(|solver| {
            self.value_encoder
                .project_field(parent_ty, &value, index, solver)
        })
        .map_err(|err| self.unsupported_result(span, err))
    }

    fn ref_deref(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&SpecTy::Ref(Box::new(inner_ty.clone())))?;
        self.decode_composite_field(&encoding, value, 0, span)
    }

    fn ref_ptr(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&SpecTy::Ref(Box::new(inner_ty.clone())))?;
        self.decode_composite_field(&encoding, value, 1, span)
    }

    fn mut_cur(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_composite_field(&encoding, value, 0, span)
    }

    fn mut_fin(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_composite_field(&encoding, value, 1, span)
    }

    fn mut_ptr(
        &self,
        value: &SymValue,
        inner_ty: &SpecTy,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&SpecTy::Mut(Box::new(inner_ty.clone())))?;
        self.decode_composite_field(&encoding, value, 2, span)
    }

    fn ptr_addr(&self, value: &SymValue, span: Span) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&ptr_spec_ty())?;
        self.decode_composite_field(&encoding, value, 0, span)
    }

    fn ptr_prov(&self, value: &SymValue, span: Span) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&ptr_spec_ty())?;
        self.decode_composite_field(&encoding, value, 1, span)
    }

    fn ptr_ty(&self, value: &SymValue, span: Span) -> Result<SymValue, VerificationResult> {
        let encoding = self.composite_encoding(&ptr_spec_ty())?;
        self.decode_composite_field(&encoding, value, 2, span)
    }

    fn reference_ptr_formula(
        &self,
        ptr: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let prov = self.ptr_prov(ptr, span)?;
        let none = self.construct_option_none(provenance_spec_ty())?;
        let has_prov = self
            .eq_for_spec_ty(&option_spec_ty(provenance_spec_ty()), &prov, &none, span)?
            .not();
        Ok(bool_and(vec![
            self.resolve_formula_for_spec_ty(&ptr_spec_ty(), ptr, span)?,
            has_prov,
        ]))
    }

    fn ptr_with_ty(
        &self,
        value: &SymValue,
        pointee_ty: Ty<'tcx>,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        let addr = self.ptr_addr(value, span)?;
        let prov = self.ptr_prov(value, span)?;
        let ty = self.rust_ty_model_value(pointee_ty);
        self.construct_ptr(addr, prov, ty)
    }

    fn builtin_nat_decls(&self, span: Span) -> Result<Rc<BuiltinNatDecls>, VerificationResult> {
        if let Some(decls) = self.builtin_nat_decls.borrow().as_ref().cloned() {
            return Ok(decls);
        }
        let decls = with_solver(|solver| {
            let nat_ty = SpecTy::Enum {
                name: "Nat".to_owned(),
                args: vec![],
            };
            let nat_composite = self.value_encoder.composite_encoding(&nat_ty, solver)?;
            let (zero_index, zero_ctor) = nat_composite
                .constructors
                .iter()
                .enumerate()
                .find(|(_, ctor)| ctor.fields.is_empty())
                .ok_or_else(|| "Nat is missing `Zero`".to_owned())?;
            let (succ_index, succ_ctor) = nat_composite
                .constructors
                .iter()
                .enumerate()
                .find(|(_, ctor)| ctor.fields.len() == 1)
                .ok_or_else(|| "Nat is missing `Succ`".to_owned())?;

            let nat_to_int = RecFuncDecl::new(
                "builtin_nat_to_int",
                &[self.value_encoder.value_sort()],
                &Sort::int(),
            );
            let int_to_nat = RecFuncDecl::new(
                "builtin_int_to_nat",
                &[&Sort::int()],
                self.value_encoder.value_sort(),
            );

            let int_arg = Int::new_const(self.fresh_name("builtin_int_to_nat_arg"));
            let zero_value = zero_ctor.symbol.apply(&[]);
            let int_minus_one = int_arg.clone() - Int::from_i64(1);
            let succ_tail = int_to_nat.apply(&[&int_minus_one]);
            let succ_value = succ_ctor.symbol.apply(&[&succ_tail]);
            let int_to_nat_body = int_arg.le(0).ite(&zero_value, &succ_value);
            int_to_nat.add_def(&[&int_arg], &int_to_nat_body);

            let nat_arg = Dynamic::new_const(
                self.fresh_name("builtin_nat_to_int_arg"),
                self.value_encoder.value_sort(),
            );
            let nat_value = SymValue::new(nat_arg.clone());
            let zero_case =
                self.value_encoder
                    .tag_formula(&nat_composite, zero_index, &nat_value)?;
            let succ_field = self.value_encoder.project_composite_ctor_field(
                &nat_composite,
                succ_index,
                &nat_value,
                0,
            )?;
            let succ_int = nat_to_int
                .apply(&[succ_field.ast()])
                .as_int()
                .ok_or_else(|| "builtin_nat_to_int must return Int".to_owned())?;
            let nat_to_int_body = zero_case.ite(&Int::from_i64(0), &(Int::from_i64(1) + succ_int));
            nat_to_int.add_def(&[&nat_arg], &nat_to_int_body);

            Ok(Rc::new(BuiltinNatDecls {
                nat_to_int,
                int_to_nat,
            }))
        })
        .map_err(|err: String| self.unsupported_result(span, err))?;
        self.builtin_nat_decls.replace(Some(decls.clone()));
        Ok(decls)
    }

    fn nat_to_int_term(&self, value: &SymValue, span: Span) -> Result<Int, VerificationResult> {
        if let Some(n) = self.try_concrete_nat_usize(value, span)? {
            return Ok(Int::from_u64(n));
        }
        let decls = self.builtin_nat_decls(span)?;
        decls
            .nat_to_int
            .apply(&[value.ast()])
            .as_int()
            .ok_or_else(|| {
                self.unsupported_result(span, "builtin_nat_to_int must return Int".to_owned())
            })
    }

    fn int_to_nat_value(&self, value: &Int, span: Span) -> Result<SymValue, VerificationResult> {
        let decls = self.builtin_nat_decls(span)?;
        Ok(SymValue::new(decls.int_to_nat.apply(&[value])))
    }

    fn nat_spec_ty() -> SpecTy {
        SpecTy::Enum {
            name: "Nat".to_owned(),
            args: vec![],
        }
    }

    fn nat_ctor_indices(&self) -> Result<(usize, usize), VerificationResult> {
        let composite = self.composite_encoding(&Self::nat_spec_ty())?;
        let zero = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| ctor.fields.is_empty())
            .map(|(index, _)| index)
            .ok_or_else(|| {
                self.unsupported_result(self.report_span(), "Nat is missing `Zero`".to_owned())
            })?;
        let succ = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| ctor.fields.len() == 1)
            .map(|(index, _)| index)
            .ok_or_else(|| {
                self.unsupported_result(self.report_span(), "Nat is missing `Succ`".to_owned())
            })?;
        Ok((zero, succ))
    }

    fn try_concrete_nat_usize(
        &self,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<u64>, VerificationResult> {
        let nat_ty = Self::nat_spec_ty();
        let (zero, succ) = self.nat_ctor_indices()?;
        match self.ground_ctor_index(&nat_ty, value, span)? {
            Some(index) if index == zero => Ok(Some(0)),
            Some(index) if index == succ => {
                let composite = self.composite_encoding(&nat_ty)?;
                let tail = self
                    .value_encoder
                    .project_composite_ctor_field(&composite, succ, value, 0)
                    .map_err(|err| self.unsupported_result(span, err))?;
                Ok(self.try_concrete_nat_usize(&tail, span)?.map(|n| n + 1))
            }
            _ => Ok(None),
        }
    }

    fn concrete_nat_value(&self, n: u64) -> Result<SymValue, VerificationResult> {
        let nat_ty = Self::nat_spec_ty();
        let (zero, succ) = self.nat_ctor_indices()?;
        let mut value = self.construct_composite_ctor(&nat_ty, zero, &[])?;
        for _ in 0..n {
            value = self.construct_composite_ctor(&nat_ty, succ, &[value])?;
        }
        Ok(value)
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
        Ok(self.value_encoder.wrap_int(&int))
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
        Ok(self.value_encoder.wrap_bool(&bool_not(in_range)))
    }

    fn spec_ty_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<Bool>, VerificationResult> {
        match ty {
            SpecTy::Bool => Ok(None),
            SpecTy::RustTy => Ok(None),
            SpecTy::Int
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
            | SpecTy::Usize => Ok(self.int_range_formula_for_int(
                self.value_encoder
                    .int_bounds(ty)
                    .map_err(|err| self.unsupported_result(span, err))?,
                &self.value_int_data(value),
            )),
            SpecTy::Seq(_) => Ok(None),
            SpecTy::Ref(inner) => {
                let composite = self.composite_encoding(ty)?;
                let deref = self.decode_composite_field(&composite, value, 0, span)?;
                let ptr = self.decode_composite_field(&composite, value, 1, span)?;
                let mut formulas = vec![
                    self.composite_tag_formula_for_encoding(&composite, value, 0, span)?,
                    self.reference_ptr_formula(&ptr, span)?,
                ];
                if let Some(formula) = self.spec_ty_formula(inner, &deref, span)? {
                    formulas.push(formula);
                }
                Ok(Some(bool_and(formulas)))
            }
            SpecTy::Mut(inner) => {
                let composite = self.composite_encoding(ty)?;
                let current = self.decode_composite_field(&composite, value, 0, span)?;
                let ptr = self.decode_composite_field(&composite, value, 2, span)?;
                let mut formulas = vec![
                    self.composite_tag_formula_for_encoding(&composite, value, 0, span)?,
                    self.reference_ptr_formula(&ptr, span)?,
                ];
                if let Some(formula) = self.spec_ty_formula(inner, &current, span)? {
                    formulas.push(formula);
                }
                Ok(Some(bool_and(formulas)))
            }
            SpecTy::Tuple(items) => {
                let composite = self.composite_encoding(ty)?;
                let mut formulas =
                    vec![self.composite_tag_formula_for_encoding(&composite, value, 0, span)?];
                for (index, field_ty) in items.iter().enumerate() {
                    let field = self.decode_composite_field(&composite, value, index, span)?;
                    if let Some(formula) = self.spec_ty_formula(field_ty, &field, span)? {
                        formulas.push(formula);
                    }
                }
                Ok(Some(bool_and(formulas)))
            }
            SpecTy::Struct(struct_ty) => {
                let composite = self.composite_encoding(ty)?;
                if let Some(formula) =
                    self.direct_struct_invariant_formula(&composite, struct_ty, value, span)?
                {
                    return Ok(Some(formula));
                }
                let mut formulas =
                    vec![self.composite_tag_formula_for_encoding(&composite, value, 0, span)?];
                for (index, field) in struct_ty.fields.iter().enumerate() {
                    let field_value =
                        self.decode_composite_field(&composite, value, index, span)?;
                    if let Some(formula) = self.spec_ty_formula(&field.ty, &field_value, span)? {
                        formulas.push(formula);
                    }
                }
                Ok(Some(bool_and(formulas)))
            }
            SpecTy::Enum { .. } => self.enum_invariant_formula(ty, value, span).map(Some),
            SpecTy::TypeParam(_) => Ok(None),
        }
    }

    fn direct_struct_invariant_formula(
        &self,
        composite: &CompositeEncoding,
        struct_ty: &crate::spec::StructTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Option<Bool>, VerificationResult> {
        let Ok(ctor) = composite.single_constructor() else {
            return Ok(None);
        };
        if value.dynamic().decl().name() != ctor.symbol.name() {
            return Ok(None);
        }
        let children = value.dynamic().children();
        if children.len() != struct_ty.fields.len() {
            return Ok(None);
        }
        let mut formulas = Vec::new();
        for (field, child) in struct_ty.fields.iter().zip(children) {
            let child = SymValue::new(child);
            if let Some(formula) = self.spec_ty_formula(&field.ty, &child, span)? {
                formulas.push(formula);
            }
        }
        Ok(Some(bool_and(formulas)))
    }

    fn resolve_formula_for_spec_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        match ty {
            SpecTy::Bool
            | SpecTy::RustTy
            | SpecTy::Int
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
            SpecTy::Seq(_) => Ok(Bool::from_bool(true)),
            SpecTy::Ref(_) => {
                let composite = self.composite_encoding(ty)?;
                let ptr = self.decode_composite_field(&composite, value, 1, span)?;
                Ok(bool_and(vec![
                    self.composite_tag_formula_for_encoding(&composite, value, 0, span)?,
                    self.reference_ptr_formula(&ptr, span)?,
                ]))
            }
            SpecTy::Mut(inner) => {
                let composite = self.composite_encoding(ty)?;
                let cur = self.decode_composite_field(&composite, value, 0, span)?;
                let fin = self.decode_composite_field(&composite, value, 1, span)?;
                let ptr = self.decode_composite_field(&composite, value, 2, span)?;
                Ok(bool_and(vec![
                    self.composite_tag_formula_for_encoding(&composite, value, 0, span)?,
                    self.eq_for_spec_ty(inner, &cur, &fin, span)?,
                    self.resolve_formula_for_spec_ty(inner, &cur, span)?,
                    self.resolve_formula_for_spec_ty(inner, &fin, span)?,
                    self.reference_ptr_formula(&ptr, span)?,
                ]))
            }
            SpecTy::Tuple(items) => {
                let composite = self.composite_encoding(ty)?;
                let mut formulas = Vec::with_capacity(items.len() + 1);
                formulas.push(self.composite_tag_formula_for_encoding(&composite, value, 0, span)?);
                for (index, field_ty) in items.iter().enumerate() {
                    let field = self.decode_composite_field(&composite, value, index, span)?;
                    formulas.push(self.resolve_formula_for_spec_ty(field_ty, &field, span)?);
                }
                Ok(bool_and(formulas))
            }
            SpecTy::Struct(struct_ty) => {
                let composite = self.composite_encoding(ty)?;
                if struct_ty.name == "Ptr" {
                    return self.composite_tag_formula_for_encoding(&composite, value, 0, span);
                }
                let mut formulas = Vec::with_capacity(struct_ty.fields.len() + 1);
                formulas.push(self.composite_tag_formula_for_encoding(&composite, value, 0, span)?);
                for (index, field) in struct_ty.fields.iter().enumerate() {
                    let field_value =
                        self.decode_composite_field(&composite, value, index, span)?;
                    formulas.push(self.resolve_formula_for_spec_ty(
                        &field.ty,
                        &field_value,
                        span,
                    )?);
                }
                Ok(bool_and(formulas))
            }
            SpecTy::Enum { .. } => self.enum_invariant_formula(ty, value, span),
            SpecTy::TypeParam(_) => Ok(Bool::from_bool(true)),
        }
    }

    fn enum_invariant_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let composite = self.composite_encoding(ty)?;
        let decl_name = value.dynamic().decl().name();
        if let Some((ctor_index, ctor)) = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| decl_name == ctor.symbol.name())
        {
            let mut formulas =
                vec![self.composite_tag_formula_for_encoding(&composite, value, ctor_index, span)?];
            for (field_index, field) in ctor.fields.iter().enumerate() {
                let field_value = self.decode_composite_ctor_field(
                    &composite,
                    ctor_index,
                    value,
                    field_index,
                    span,
                )?;
                if let Some(formula) = self.spec_ty_formula(&field.ty, &field_value, span)? {
                    formulas.push(formula);
                }
            }
            return Ok(bool_and(formulas));
        }
        self.named_invariant_formula(ty, value, span)
    }

    fn named_invariant_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        with_solver(|solver| {
            let invariant = self
                .value_encoder
                .named_invariant(ty, solver)?
                .ok_or_else(|| format!("missing named invariant for {ty:?}"))?;
            Ok(invariant
                .apply(&[value.ast()])
                .as_bool()
                .expect("named invariant predicate"))
        })
        .map_err(|err: String| self.unsupported_result(span, err))
    }

    fn decode_composite_field(
        &self,
        encoding: &CompositeEncoding,
        value: &SymValue,
        index: usize,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        self.value_encoder
            .project_composite_field(encoding, value, index)
            .map_err(|err| self.unsupported_result(span, err))
    }

    fn decode_composite_ctor_field(
        &self,
        encoding: &CompositeEncoding,
        ctor_index: usize,
        value: &SymValue,
        index: usize,
        span: Span,
    ) -> Result<SymValue, VerificationResult> {
        self.value_encoder
            .project_composite_ctor_field(encoding, ctor_index, value, index)
            .map_err(|err| self.unsupported_result(span, err))
    }

    fn composite_tag_formula_for_encoding(
        &self,
        encoding: &CompositeEncoding,
        value: &SymValue,
        ctor_index: usize,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        self.value_encoder
            .tag_formula(encoding, ctor_index, value)
            .map_err(|err| self.unsupported_result(span, err))
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
        self.assert_constraint(state, formula, span, span_text(self.tcx, span), message)
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

    fn fail_result(&self, span: Span, message: String) -> VerificationResult {
        VerificationResult {
            function: self.report_function(),
            status: VerificationStatus::Fail,
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

    fn contract_req_formula(
        &self,
        contract: &FunctionContract,
        env: &CallEnv,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let mut formulas =
            vec![self.contract_expr_to_bool(&env.current, &env.spec, &contract.req.condition)?];
        formulas.extend(self.auto_contract_formulas(contract, env, span, false)?);
        Ok(bool_and(formulas))
    }

    fn contract_ens_formula(
        &self,
        contract: &FunctionContract,
        env: &CallEnv,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
        let mut formulas =
            vec![self.contract_expr_to_bool(&env.current, &env.spec, &contract.ens)?];
        formulas.extend(self.auto_contract_formulas(contract, env, span, true)?);
        Ok(bool_and(formulas))
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

#[derive(Debug, Clone)]
struct LemmaExecState {
    current: HashMap<String, SymValue>,
    state: State,
}

impl CallEnv {
    fn for_function<'tcx>(
        verifier: &Verifier<'tcx>,
        state: &State,
        contract: &FunctionContract,
    ) -> Result<Self, VerificationResult> {
        let mut current = HashMap::new();
        let mut spec = state.spec_env.clone();
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
            current.insert("result".to_owned(), result.clone());
            spec.insert("result".to_owned(), result);
        }
        Ok(Self { current, spec })
    }
}

fn collect_needed_pure_fns(
    prepass: &DirectivePrepass,
    lemmas: &[TypedLemmaDef],
    pure_fns: &[TypedPureFnDef],
) -> Vec<TypedPureFnDef> {
    let pure_fn_defs = pure_fns
        .iter()
        .cloned()
        .map(|pure_fn| (pure_fn.name.clone(), pure_fn))
        .collect::<HashMap<_, _>>();
    let lemma_map = lemmas
        .iter()
        .cloned()
        .map(|lemma| (lemma.name.clone(), lemma))
        .collect::<HashMap<_, _>>();
    let mut needed = BTreeSet::new();
    collect_directive_prepass_pure_fn_refs(prepass, &lemma_map, &mut needed);
    let mut agenda = needed.iter().cloned().collect::<VecDeque<_>>();
    while let Some(name) = agenda.pop_front() {
        let Some(pure_fn) = pure_fn_defs.get(&name) else {
            continue;
        };
        let mut refs = BTreeSet::new();
        collect_typed_expr_pure_fn_refs(&pure_fn.body, &mut refs);
        for reference in refs {
            if needed.insert(reference.clone()) {
                agenda.push_back(reference);
            }
        }
    }
    pure_fns
        .iter()
        .filter(|pure_fn| needed.contains(&pure_fn.name))
        .cloned()
        .collect()
}

fn collect_directive_prepass_pure_fn_refs(
    prepass: &DirectivePrepass,
    lemmas: &HashMap<String, TypedLemmaDef>,
    out: &mut BTreeSet<String>,
) {
    if let Some(contract) = &prepass.function_contract {
        collect_normalized_predicate_pure_fn_refs(&contract.req, out);
        collect_typed_expr_pure_fn_refs(&contract.ens, out);
    }
    for loop_contract in prepass.loop_contracts.by_header.values() {
        collect_typed_expr_pure_fn_refs(&loop_contract.invariant, out);
    }
    let mut needed_lemmas = VecDeque::new();
    for directives in prepass.control_point_directives.by_control_point.values() {
        for directive in directives {
            match directive {
                ControlPointDirective::Let(binding) => {
                    collect_typed_expr_pure_fn_refs(&binding.binding.value, out);
                }
                ControlPointDirective::Assert(assertion) => {
                    collect_normalized_predicate_pure_fn_refs(&assertion.assertion, out);
                }
                ControlPointDirective::Assume(assumption) => {
                    collect_typed_expr_pure_fn_refs(&assumption.assumption, out);
                }
                ControlPointDirective::LemmaCall(call) => {
                    for arg in &call.args {
                        collect_typed_expr_pure_fn_refs(arg, out);
                    }
                    needed_lemmas.push_back(call.lemma_name.clone());
                }
            }
        }
    }
    let mut seen_lemmas = BTreeSet::new();
    while let Some(lemma_name) = needed_lemmas.pop_front() {
        if !seen_lemmas.insert(lemma_name.clone()) {
            continue;
        }
        let Some(lemma) = lemmas.get(&lemma_name) else {
            continue;
        };
        collect_normalized_predicate_pure_fn_refs(&lemma.req, out);
        collect_typed_expr_pure_fn_refs(&lemma.ens, out);
    }
}

fn collect_normalized_predicate_pure_fn_refs(
    predicate: &NormalizedPredicate,
    out: &mut BTreeSet<String>,
) {
    for binding in &predicate.bindings {
        collect_typed_expr_pure_fn_refs(&binding.value, out);
    }
    collect_typed_expr_pure_fn_refs(&predicate.condition, out);
}

fn collect_typed_expr_pure_fn_refs(expr: &TypedExpr, out: &mut BTreeSet<String>) {
    match &expr.kind {
        TypedExprKind::Bool(_)
        | TypedExprKind::Int(_)
        | TypedExprKind::Var(_)
        | TypedExprKind::RustVar(_)
        | TypedExprKind::RustType(_) => {}
        TypedExprKind::SeqLit(items) | TypedExprKind::StructLit { fields: items } => {
            for item in items {
                collect_typed_expr_pure_fn_refs(item, out);
            }
        }
        TypedExprKind::Match {
            scrutinee,
            arms,
            default,
        } => {
            collect_typed_expr_pure_fn_refs(scrutinee, out);
            for arm in arms {
                collect_typed_expr_pure_fn_refs(&arm.body, out);
            }
            if let Some(default) = default {
                collect_typed_expr_pure_fn_refs(default, out);
            }
        }
        TypedExprKind::PureCall { func, args } => {
            out.insert(func.clone());
            for arg in args {
                collect_typed_expr_pure_fn_refs(arg, out);
            }
        }
        TypedExprKind::CtorCall { args, .. } => {
            for arg in args {
                collect_typed_expr_pure_fn_refs(arg, out);
            }
        }
        TypedExprKind::Field { base, .. }
        | TypedExprKind::TupleField { base, .. }
        | TypedExprKind::Unary { arg: base, .. } => collect_typed_expr_pure_fn_refs(base, out),
        TypedExprKind::Index { base, index } => {
            collect_typed_expr_pure_fn_refs(base, out);
            collect_typed_expr_pure_fn_refs(index, out);
        }
        TypedExprKind::Binary { lhs, rhs, .. } => {
            collect_typed_expr_pure_fn_refs(lhs, out);
            collect_typed_expr_pure_fn_refs(rhs, out);
        }
    }
}

fn init_z3() {
    Z3_INIT.call_once(|| {
        z3::set_global_param("model", "true");
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");
    });
}

fn build_solver() -> Solver {
    init_z3();
    let solver = Solver::new();
    let mut params = z3::Params::new();
    params.set_u32("timeout", SOLVER_TIMEOUT_MS);
    solver.set_params(&params);
    solver
}

fn rebuild_solver() {
    GLOBAL_SOLVER.with(|solver| {
        *solver.borrow_mut() = build_solver();
    });
}

fn reset_solver() {
    with_solver(|solver| {
        solver.reset();
    });
}

fn with_solver<T>(f: impl FnOnce(&Solver) -> T) -> T {
    GLOBAL_SOLVER.with(|solver| f(&solver.borrow()))
}

fn with_z3_deadline<T>(budget: Duration, f: impl FnOnce() -> T) -> (T, bool) {
    let ctx = Context::thread_local();
    let handle = ctx.handle();
    let (done_tx, done_rx) = mpsc::channel::<()>();
    thread::scope(|scope| {
        let watchdog = scope.spawn(move || {
            if done_rx.recv_timeout(budget).is_err() {
                handle.interrupt();
                true
            } else {
                false
            }
        });
        let result = f();
        let _ = done_tx.send(());
        let timed_out = watchdog.join().expect("watchdog thread");
        (result, timed_out)
    })
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

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.lo() <= inner.lo() && inner.hi() <= outer.hi()
}

fn spec_ty_contains_mut_ref(ty: &SpecTy) -> bool {
    match ty {
        SpecTy::Mut(_) => true,
        SpecTy::Ref(inner) => spec_ty_contains_mut_ref(inner),
        SpecTy::Seq(inner) => spec_ty_contains_mut_ref(inner),
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

#[cfg(test)]
mod tests {
    use super::{collect_needed_pure_fns, rebuild_solver, with_solver};
    use crate::prepass::{
        AssertionContract, ControlPointDirective, ControlPointDirectives, DirectivePrepass,
        FunctionContract, LoopContracts, NormalizedPredicate, ResolvedExprEnv, TypedPureFnDef,
    };
    use crate::spec::{SpecTy, TypedExpr, TypedExprKind};
    use z3::ast::Int;
    use z3::{Config, SatResult};

    #[test]
    fn thread_local_solver_distinguishes_sat_from_unsat() {
        rebuild_solver();
        let x = Int::new_const("x");
        let sat = with_solver(|solver| {
            solver.push();
            solver.assert(x.eq(1));
            let result = solver.check();
            solver.pop(1);
            result
        });
        assert_eq!(sat, SatResult::Sat);

        let unsat = with_solver(|solver| {
            solver.push();
            solver.assert(x.eq(1));
            solver.assert(x.eq(2));
            let result = solver.check();
            solver.pop(1);
            result
        });
        assert_eq!(unsat, SatResult::Unsat);
    }

    #[test]
    fn with_z3_config_solver_distinguishes_sat_from_unsat() {
        let result = z3::with_z3_config(&Config::new(), || {
            rebuild_solver();
            let x = Int::new_const("x");
            let sat = with_solver(|solver| {
                solver.push();
                solver.assert(x.eq(1));
                let result = solver.check();
                solver.pop(1);
                result
            });
            let unsat = with_solver(|solver| {
                solver.push();
                solver.assert(x.eq(1));
                solver.assert(x.eq(2));
                let result = solver.check();
                solver.pop(1);
                result
            });
            (sat, unsat)
        });
        assert_eq!(result.0, SatResult::Sat);
        assert_eq!(result.1, SatResult::Unsat);
    }

    #[test]
    fn collect_needed_pure_fns_depends_only_on_live_prepass_output() {
        let bool_true = TypedExpr {
            ty: SpecTy::Bool,
            kind: TypedExprKind::Bool(true),
        };
        let id_call = TypedExpr {
            ty: SpecTy::I32,
            kind: TypedExprKind::PureCall {
                func: "id".to_owned(),
                args: vec![TypedExpr {
                    ty: SpecTy::I32,
                    kind: TypedExprKind::Int(crate::spec::IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(crate::spec::IntSuffix::I32),
                    }),
                }],
            },
        };
        let prepass = DirectivePrepass {
            loop_contracts: LoopContracts::default(),
            control_point_directives: ControlPointDirectives {
                by_control_point: std::collections::HashMap::from([(
                    (rustc_middle::mir::BasicBlock::from_usize(0), 0usize),
                    vec![ControlPointDirective::Assert(AssertionContract {
                        assertion: NormalizedPredicate {
                            bindings: Vec::new(),
                            condition: id_call,
                        },
                        resolution: ResolvedExprEnv::default(),
                        assertion_span: "fixture.rs:1:1".to_owned(),
                    })],
                )]),
            },
            function_contract: Some(FunctionContract {
                params: Vec::new(),
                req: NormalizedPredicate {
                    bindings: Vec::new(),
                    condition: bool_true.clone(),
                },
                req_span: "fixture.rs:1:1".to_owned(),
                ens: bool_true,
                ens_span: "fixture.rs:1:1".to_owned(),
                result: SpecTy::Bool,
            }),
            unsafe_blocks: Vec::new(),
        };
        let pure_fns = vec![
            TypedPureFnDef {
                name: "id".to_owned(),
                params: Vec::new(),
                body: TypedExpr {
                    ty: SpecTy::I32,
                    kind: TypedExprKind::Int(crate::spec::IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(crate::spec::IntSuffix::I32),
                    }),
                },
            },
            TypedPureFnDef {
                name: "unused".to_owned(),
                params: Vec::new(),
                body: TypedExpr {
                    ty: SpecTy::I32,
                    kind: TypedExprKind::Int(crate::spec::IntLiteral {
                        digits: "0".to_owned(),
                        suffix: Some(crate::spec::IntSuffix::I32),
                    }),
                },
            },
        ];
        let needed = collect_needed_pure_fns(&prepass, &[], &pure_fns);
        assert_eq!(needed.len(), 1);
        assert_eq!(needed[0].name, "id");
    }
}
