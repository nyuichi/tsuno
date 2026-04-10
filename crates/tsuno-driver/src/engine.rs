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
use z3::ast::{Ast, Bool, Datatype, Int};
use z3::{
    DatatypeAccessor, DatatypeBuilder, DatatypeSort, RecFuncDecl, SatResult, Solver, SortKind,
};

use crate::prepass::{
    AssertionContracts, AssumptionContracts, FunctionContract, LoopContract, LoopContracts,
    ResolvedExprEnv, compute_directives, compute_function_contracts,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{BinaryOp, Expr, UnaryOp};

thread_local! {
    static GLOBAL_SOLVER: Solver = {
        init_z3();
        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);
        solver
    };
    static VALUE_ENCODING: ValueEncoding = {
        init_z3();
        ValueEncoding::new()
    };
}

static Z3_INIT: Once = Once::new();

struct ValueEncoding {
    sort: DatatypeSort,
    eqv: RecFuncDecl,
    add: RecFuncDecl,
    sub: RecFuncDecl,
    mul: RecFuncDecl,
    neg: RecFuncDecl,
    not: RecFuncDecl,
    andv: RecFuncDecl,
    orv: RecFuncDecl,
    ltv: RecFuncDecl,
    lev: RecFuncDecl,
    gtv: RecFuncDecl,
    gev: RecFuncDecl,
    is_true: RecFuncDecl,
}

impl ValueEncoding {
    fn new() -> Self {
        let sort = DatatypeBuilder::new("value")
            .variant("error", vec![])
            .variant("nil", vec![])
            .variant(
                "cons",
                vec![
                    ("car", DatatypeAccessor::datatype("value")),
                    ("cdr", DatatypeAccessor::datatype("value")),
                ],
            )
            .variant("int", vec![("i", DatatypeAccessor::Sort(z3::Sort::int()))])
            .variant(
                "bool",
                vec![("b", DatatypeAccessor::Sort(z3::Sort::bool()))],
            )
            .finish();
        let value_sort = sort.sort.clone();
        let encoding = Self {
            sort,
            eqv: RecFuncDecl::new("eqv", &[&value_sort, &value_sort], &value_sort),
            add: RecFuncDecl::new("addv", &[&value_sort, &value_sort], &value_sort),
            sub: RecFuncDecl::new("subv", &[&value_sort, &value_sort], &value_sort),
            mul: RecFuncDecl::new("mulv", &[&value_sort, &value_sort], &value_sort),
            neg: RecFuncDecl::new("negv", &[&value_sort], &value_sort),
            not: RecFuncDecl::new("notv", &[&value_sort], &value_sort),
            andv: RecFuncDecl::new("andv", &[&value_sort, &value_sort], &value_sort),
            orv: RecFuncDecl::new("orv", &[&value_sort, &value_sort], &value_sort),
            ltv: RecFuncDecl::new("ltv", &[&value_sort, &value_sort], &value_sort),
            lev: RecFuncDecl::new("lev", &[&value_sort, &value_sort], &value_sort),
            gtv: RecFuncDecl::new("gtv", &[&value_sort, &value_sort], &value_sort),
            gev: RecFuncDecl::new("gev", &[&value_sort, &value_sort], &value_sort),
            is_true: RecFuncDecl::new("is_true", &[&value_sort], &z3::Sort::bool()),
        };
        encoding.define_functions();
        encoding
    }

    fn error(&self) -> Datatype {
        self.sort.variants[0]
            .constructor
            .apply(&[])
            .as_datatype()
            .unwrap()
    }

    fn nil(&self) -> Datatype {
        self.sort.variants[1]
            .constructor
            .apply(&[])
            .as_datatype()
            .unwrap()
    }

    fn cons(&self, car: &Datatype, cdr: &Datatype) -> Datatype {
        self.sort.variants[2]
            .constructor
            .apply(&[car, cdr])
            .as_datatype()
            .unwrap()
    }

    fn int(&self, value: i64) -> Datatype {
        self.sort.variants[3]
            .constructor
            .apply(&[&Int::from_i64(value)])
            .as_datatype()
            .unwrap()
    }

    fn bool(&self, value: bool) -> Datatype {
        self.wrap_bool(&Bool::from_bool(value))
    }

    fn wrap_bool(&self, value: &Bool) -> Datatype {
        value.ite(&self.bool_true(), &self.bool_false())
    }

    fn wrap_int(&self, value: &Int) -> Datatype {
        self.sort.variants[3]
            .constructor
            .apply(&[value])
            .as_datatype()
            .unwrap()
    }

    fn bool_true(&self) -> Datatype {
        self.sort.variants[4]
            .constructor
            .apply(&[&Bool::from_bool(true)])
            .as_datatype()
            .unwrap()
    }

    fn bool_false(&self) -> Datatype {
        self.sort.variants[4]
            .constructor
            .apply(&[&Bool::from_bool(false)])
            .as_datatype()
            .unwrap()
    }

    fn fresh(&self, name: &str) -> Datatype {
        Datatype::new_const(name, &self.sort.sort)
    }

    fn list(&self, values: &[Datatype]) -> Datatype {
        values
            .iter()
            .rev()
            .fold(self.nil(), |tail, head| self.cons(head, &tail))
    }

    fn is_error(&self, value: &Datatype) -> Bool {
        self.sort.variants[0]
            .tester
            .apply(&[value])
            .as_bool()
            .unwrap()
    }

    fn is_nil(&self, value: &Datatype) -> Bool {
        self.sort.variants[1]
            .tester
            .apply(&[value])
            .as_bool()
            .unwrap()
    }

    fn is_cons(&self, value: &Datatype) -> Bool {
        self.sort.variants[2]
            .tester
            .apply(&[value])
            .as_bool()
            .unwrap()
    }

    fn is_int(&self, value: &Datatype) -> Bool {
        self.sort.variants[3]
            .tester
            .apply(&[value])
            .as_bool()
            .unwrap()
    }

    fn is_bool_value(&self, value: &Datatype) -> Bool {
        self.sort.variants[4]
            .tester
            .apply(&[value])
            .as_bool()
            .unwrap()
    }

    fn car(&self, value: &Datatype) -> Datatype {
        self.sort.variants[2].accessors[0]
            .apply(&[value])
            .as_datatype()
            .unwrap()
    }

    fn cdr(&self, value: &Datatype) -> Datatype {
        self.sort.variants[2].accessors[1]
            .apply(&[value])
            .as_datatype()
            .unwrap()
    }

    fn int_data(&self, value: &Datatype) -> Int {
        self.sort.variants[3].accessors[0]
            .apply(&[value])
            .as_int()
            .unwrap()
    }

    fn bool_data(&self, value: &Datatype) -> Bool {
        self.sort.variants[4].accessors[0]
            .apply(&[value])
            .as_bool()
            .unwrap()
    }

    fn eqv(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.eqv.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn add(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.add.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn sub(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.sub.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn mul(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.mul.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn neg(&self, value: &Datatype) -> Datatype {
        self.neg.apply(&[value]).as_datatype().unwrap()
    }

    fn notv(&self, value: &Datatype) -> Datatype {
        self.not.apply(&[value]).as_datatype().unwrap()
    }

    fn andv(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.andv.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn orv(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.orv.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn ltv(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.ltv.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn lev(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.lev.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn gtv(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.gtv.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn gev(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        self.gev.apply(&[lhs, rhs]).as_datatype().unwrap()
    }

    fn is_true(&self, value: &Datatype) -> Bool {
        self.is_true.apply(&[value]).as_bool().unwrap()
    }

    fn nth(&self, value: &Datatype, index: usize) -> Datatype {
        let mut current = value.clone();
        for _ in 0..index {
            current = self.cdr(&current);
        }
        self.car(&current)
    }

    fn pair_first(&self, value: &Datatype) -> Datatype {
        self.nth(value, 0)
    }

    fn pair_second(&self, value: &Datatype) -> Datatype {
        self.nth(value, 1)
    }

    fn define_functions(&self) {
        self.define_binary_bool_value(&self.andv, |lhs, rhs| Bool::and(&[lhs, rhs]));
        self.define_binary_bool_value(&self.orv, |lhs, rhs| Bool::or(&[lhs, rhs]));
        self.define_not();
        self.define_binary_int_value(&self.add, |lhs, rhs| lhs + rhs);
        self.define_binary_int_value(&self.sub, |lhs, rhs| lhs - rhs);
        self.define_binary_int_value(&self.mul, |lhs, rhs| lhs * rhs);
        self.define_neg();
        self.define_binary_int_pred(&self.ltv, |lhs, rhs| lhs.lt(rhs));
        self.define_binary_int_pred(&self.lev, |lhs, rhs| lhs.le(rhs));
        self.define_binary_int_pred(&self.gtv, |lhs, rhs| lhs.gt(rhs));
        self.define_binary_int_pred(&self.gev, |lhs, rhs| lhs.ge(rhs));
        self.define_eqv();
        self.define_is_true();
    }

    fn define_binary_bool_value(&self, func: &RecFuncDecl, op: impl Fn(&Bool, &Bool) -> Bool) {
        let x = self.fresh("x");
        let y = self.fresh("y");
        let body = bool_or(vec![self.is_error(&x), self.is_error(&y)]).ite(
            &self.error(),
            &bool_and(vec![self.is_bool_value(&x), self.is_bool_value(&y)]).ite(
                &self.wrap_bool(&op(&self.bool_data(&x), &self.bool_data(&y))),
                &self.error(),
            ),
        );
        func.add_def(&[&x, &y], &body);
    }

    fn define_binary_int_value(&self, func: &RecFuncDecl, op: impl Fn(&Int, &Int) -> Int) {
        let x = self.fresh("x");
        let y = self.fresh("y");
        let body = bool_or(vec![self.is_error(&x), self.is_error(&y)]).ite(
            &self.error(),
            &bool_and(vec![self.is_int(&x), self.is_int(&y)]).ite(
                &self.sort.variants[3]
                    .constructor
                    .apply(&[&op(&self.int_data(&x), &self.int_data(&y))])
                    .as_datatype()
                    .unwrap(),
                &self.error(),
            ),
        );
        func.add_def(&[&x, &y], &body);
    }

    fn define_binary_int_pred(&self, func: &RecFuncDecl, op: impl Fn(&Int, &Int) -> Bool) {
        let x = self.fresh("x");
        let y = self.fresh("y");
        let body = bool_or(vec![self.is_error(&x), self.is_error(&y)]).ite(
            &self.error(),
            &bool_and(vec![self.is_int(&x), self.is_int(&y)]).ite(
                &self.wrap_bool(&op(&self.int_data(&x), &self.int_data(&y))),
                &self.error(),
            ),
        );
        func.add_def(&[&x, &y], &body);
    }

    fn define_neg(&self) {
        let x = self.fresh("x");
        let body = self.is_error(&x).ite(
            &self.error(),
            &self.is_int(&x).ite(
                &self.sort.variants[3]
                    .constructor
                    .apply(&[&(Int::from_i64(0) - self.int_data(&x))])
                    .as_datatype()
                    .unwrap(),
                &self.error(),
            ),
        );
        self.neg.add_def(&[&x], &body);
    }

    fn define_not(&self) {
        let x = self.fresh("x");
        let body = self.is_error(&x).ite(
            &self.error(),
            &self
                .is_bool_value(&x)
                .ite(&self.wrap_bool(&self.bool_data(&x).not()), &self.error()),
        );
        self.not.add_def(&[&x], &body);
    }

    fn define_eqv(&self) {
        let x = self.fresh("x");
        let y = self.fresh("y");
        let body = bool_or(vec![self.is_error(&x), self.is_error(&y)]).ite(
            &self.error(),
            &self.is_nil(&x).ite(
                &self.wrap_bool(&self.is_nil(&y)),
                &bool_and(vec![self.is_cons(&x), self.is_cons(&y)]).ite(
                    &self.andv(
                        &self.eqv(&self.car(&x), &self.car(&y)),
                        &self.eqv(&self.cdr(&x), &self.cdr(&y)),
                    ),
                    &bool_and(vec![self.is_int(&x), self.is_int(&y)]).ite(
                        &self.wrap_bool(&self.int_data(&x).eq(self.int_data(&y))),
                        &bool_and(vec![self.is_bool_value(&x), self.is_bool_value(&y)]).ite(
                            &self.wrap_bool(&self.bool_data(&x).eq(self.bool_data(&y))),
                            &self.bool_false(),
                        ),
                    ),
                ),
            ),
        );
        self.eqv.add_def(&[&x, &y], &body);
    }

    fn define_is_true(&self) {
        let x = self.fresh("x");
        let body = bool_and(vec![self.is_bool_value(&x), self.bool_data(&x)]);
        self.is_true.add_def(&[&x], &body);
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
    model: BTreeMap<Local, Datatype>,
    ctrl: ControlPoint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BoolExpr {
    Const(bool),
    Value(Datatype),
    Not(Box<BoolExpr>),
}

#[derive(Debug, Clone)]
struct EvaluatedRvalue {
    value: Datatype,
    constraints: Vec<BoolExpr>,
}

pub struct Verifier<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: Body<'tcx>,
    contracts: HashMap<LocalDefId, FunctionContract>,
    function_spec_vars: HashMap<String, Datatype>,
    loop_contracts: LoopContracts,
    assertion_contracts: AssertionContracts,
    assumption_contracts: AssumptionContracts,
    prepass_error: Option<VerificationResult>,
    next_sym: Cell<usize>,
}

impl<'tcx> Verifier<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId, item_span: Span, body: Body<'tcx>) -> Self {
        let (
            loop_contracts,
            assertion_contracts,
            assumption_contracts,
            function_contract,
            spec_var_names,
            mut prepass_error,
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
        let contracts = match compute_function_contracts(tcx, Some(def_id)) {
            Ok(contracts) => contracts,
            Err(error) => {
                prepass_error.get_or_insert(error);
                HashMap::new()
            }
        };
        let next_sym = Cell::new(0);
        let function_spec_vars = instantiate_spec_vars(&next_sym, &spec_var_names);
        let mut contracts = contracts;
        if let Some(contract) = function_contract {
            contracts.insert(def_id, contract);
        }
        Self {
            tcx,
            def_id,
            body,
            contracts,
            function_spec_vars,
            loop_contracts,
            assertion_contracts,
            assumption_contracts,
            prepass_error,
            next_sym,
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
                let eval = self.eval_rvalue(&mut state, rvalue, stmt.source_info.span)?;
                self.write_place(&mut state, *place, eval.value, stmt.source_info.span)?;
                for constraint in eval.constraints {
                    let constraint = self.bool_expr_to_z3(&constraint)?;
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
                    let formula = self.bool_expr_to_z3(&formula)?;
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
                        _ => BoolExpr::Value(
                            self.value_eqv(&discr_value, &self.value_int(value as i64)),
                        ),
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
            let spec = self.instantiate_contract_spec_vars(&contract.spec_vars);
            let env = self.call_env(&state, args, contract, span, spec.clone())?;
            let req =
                self.contract_expr_to_bool(&env.current, &env.prophecy, &env.spec, &contract.req)?;
            let req = self.bool_expr_to_z3(&req)?;
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
            let ens =
                self.contract_expr_to_bool(&env.current, &env.prophecy, &env.spec, &contract.ens)?;
            let ens = self.bool_expr_to_z3(&ens)?;
            self.assume_constraint(&mut state, ens);
        } else {
            let result_ty = self.place_ty(destination);
            let result_value = self.fresh_for_rust_ty(result_ty, "opaque_result")?;
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
                let equality = self.value_is_true(&self.value_eqv(&merged_value, &incoming));
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
        if let Some(contract) = self.contracts.get(&self.def_id) {
            let env =
                CallEnv::for_function(self, &state, contract, self.function_spec_vars.clone())?;
            let req =
                self.contract_expr_to_bool(&env.current, &env.prophecy, &env.spec, &contract.req)?;
            let req = self.bool_expr_to_z3(&req)?;
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
            let formula = self.bool_expr_to_z3(&formula)?;
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
        value: &Datatype,
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
                let cur = self.value_pair_first(value);
                let fin = self.value_pair_second(value);
                if !matches!(inner.kind(), TyKind::Tuple(_)) {
                    return Ok(vec![BoolExpr::Value(self.value_eqv(&cur, &fin))]);
                }
                Ok(vec![BoolExpr::Value(self.value_eqv(&cur, &fin))])
            }
            TyKind::Ref(_, _, _) => Ok(Vec::new()),
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
                    let mut values = Vec::with_capacity(operands.len());
                    for operand in operands {
                        values.push(self.eval_operand(state, operand, span)?);
                    }
                    Ok(EvaluatedRvalue {
                        value: self.value_list(&values),
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
            value: self.value_list(&[current, final_value]),
            constraints: Vec::new(),
        })
    }

    fn create_shared_borrow(
        &self,
        state: &State,
        place: Place<'tcx>,
        span: Span,
    ) -> Result<EvaluatedRvalue, VerificationResult> {
        Ok(EvaluatedRvalue {
            value: self.read_place(state, place, ReadMode::Current, span)?,
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
            BinOp::Add => Ok(EvaluatedRvalue {
                value: self.value_add(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Sub => Ok(EvaluatedRvalue {
                value: self.value_sub(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Mul => Ok(EvaluatedRvalue {
                value: self.value_mul(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Eq => Ok(EvaluatedRvalue {
                value: self.value_eqv(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Ne => Ok(EvaluatedRvalue {
                value: self.value_not(&self.value_eqv(&lhs_value, &rhs_value)),
                constraints: Vec::new(),
            }),
            BinOp::Lt => Ok(EvaluatedRvalue {
                value: self.value_lt(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Le => Ok(EvaluatedRvalue {
                value: self.value_le(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Gt => Ok(EvaluatedRvalue {
                value: self.value_gt(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
            BinOp::Ge => Ok(EvaluatedRvalue {
                value: self.value_ge(&lhs_value, &rhs_value),
                constraints: Vec::new(),
            }),
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
        let result_value = match op {
            BinOp::Add | BinOp::AddWithOverflow => self.value_add(&lhs_value, &rhs_value),
            BinOp::Sub | BinOp::SubWithOverflow => self.value_sub(&lhs_value, &rhs_value),
            BinOp::Mul | BinOp::MulWithOverflow => self.value_mul(&lhs_value, &rhs_value),
            other => {
                return Err(self.unsupported_result(
                    span,
                    format!("unsupported checked binary operator {other:?}"),
                ));
            }
        };
        let overflow_value = self.overflow_value_for_result(result_ty, &result_value, span)?;
        Ok(EvaluatedRvalue {
            value: self.value_list(&[result_value, overflow_value]),
            constraints: Vec::new(),
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
            UnOp::Not => Ok(EvaluatedRvalue {
                value: self.value_not(&value),
                constraints: Vec::new(),
            }),
            UnOp::Neg => Ok(EvaluatedRvalue {
                value: self.value_neg(&value),
                constraints: Vec::new(),
            }),
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
    ) -> Result<Datatype, VerificationResult> {
        let value = self.read_operand(state, operand, span)?;
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
    ) -> Result<Datatype, VerificationResult> {
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
    ) -> Result<Datatype, VerificationResult> {
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
                Ok(self.value_int(self.scalar_int_to_i64(ty, value, span)?))
            }
            TyKind::Tuple(fields) if fields.is_empty() => Ok(self.value_nil()),
            _ => Err(self.unsupported_result(span, format!("unsupported constant type {ty:?}"))),
        }
    }

    fn read_place(
        &self,
        state: &State,
        place: Place<'tcx>,
        mode: ReadMode,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        let Some(root) = state.model.get(&place.local).cloned() else {
            return Err(
                self.unsupported_result(span, format!("missing local {}", place.local.as_usize()))
            );
        };
        let root_ty = self.body.local_decls[place.local].ty;
        self.read_projection(root, root_ty, place.as_ref().projection, mode, span)
    }

    fn read_projection(
        &self,
        value: Datatype,
        ty: Ty<'tcx>,
        projection: &[PlaceElem<'tcx>],
        mode: ReadMode,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        if projection.is_empty() {
            return Ok(value);
        }
        match projection[0] {
            PlaceElem::Deref => {
                let TyKind::Ref(_, inner, mutability) = ty.kind() else {
                    return Err(
                        self.unsupported_result(span, "deref of non-reference place".to_owned())
                    );
                };
                let next = if mutability.is_mut() {
                    match mode {
                        ReadMode::Current => self.value_pair_first(&value),
                        ReadMode::Final => self.value_pair_second(&value),
                    }
                } else {
                    value
                };
                self.read_projection(next, *inner, &projection[1..], mode, span)
            }
            PlaceElem::Field(field, _) => {
                let next = self.project_tuple_field(value, field.index(), span)?;
                let TyKind::Tuple(fields) = ty.kind() else {
                    return Err(self.unsupported_result(
                        span,
                        "field projection on non-tuple place".to_owned(),
                    ));
                };
                let field_ty = fields.get(field.index()).ok_or_else(|| {
                    self.unsupported_result(span, "tuple field out of range".to_owned())
                })?;
                self.read_projection(next, *field_ty, &projection[1..], mode, span)
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
        value: Datatype,
        span: Span,
    ) -> Result<(), VerificationResult> {
        let root = state
            .model
            .get(&place.local)
            .cloned()
            .unwrap_or_else(|| value.clone());
        let root_ty = self.body.local_decls[place.local].ty;
        let updated =
            self.write_projection(root, root_ty, place.as_ref().projection, value, span)?;
        state.model.insert(place.local, updated);
        Ok(())
    }

    fn write_projection(
        &self,
        value: Datatype,
        ty: Ty<'tcx>,
        projection: &[PlaceElem<'tcx>],
        replacement: Datatype,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        if projection.is_empty() {
            return Ok(replacement);
        }
        match projection[0] {
            PlaceElem::Deref => {
                let TyKind::Ref(_, inner, mutability) = ty.kind() else {
                    return Err(self.unsupported_result(
                        span,
                        "deref assignment on non-reference place".to_owned(),
                    ));
                };
                if !mutability.is_mut() {
                    return Err(self.unsupported_result(
                        span,
                        "assignment through shared reference is unsupported".to_owned(),
                    ));
                }
                let current = self.write_projection(
                    self.value_pair_first(&value),
                    *inner,
                    &projection[1..],
                    replacement,
                    span,
                )?;
                Ok(self.value_list(&[current, self.value_pair_second(&value)]))
            }
            PlaceElem::Field(field, _) => {
                let index = field.index();
                let TyKind::Tuple(fields) = ty.kind() else {
                    return Err(self.unsupported_result(
                        span,
                        "field assignment on non-tuple place".to_owned(),
                    ));
                };
                let rust_field_ty = fields.get(index).ok_or_else(|| {
                    self.unsupported_result(span, "tuple field out of range".to_owned())
                })?;
                let mut items = Vec::with_capacity(fields.len());
                for current_index in 0..fields.len() {
                    let field_value =
                        self.project_tuple_field(value.clone(), current_index, span)?;
                    if current_index == index {
                        items.push(self.write_projection(
                            field_value,
                            *rust_field_ty,
                            &projection[1..],
                            replacement.clone(),
                            span,
                        )?);
                    } else {
                        items.push(field_value);
                    }
                }
                Ok(self.value_list(&items))
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
        value: &Datatype,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        match ty.kind() {
            TyKind::Tuple(fields) => {
                let mut updated = Vec::with_capacity(fields.len());
                for (index, field_ty) in fields.iter().enumerate() {
                    let field_value = self.project_tuple_field(value.clone(), index, span)?;
                    updated.push(self.dangle_value(field_ty, &field_value, span)?);
                }
                Ok(self.value_list(&updated))
            }
            TyKind::Ref(_, inner, mutability) if mutability.is_mut() => {
                let fresh = self.fresh_for_rust_ty(*inner, "dangle")?;
                Ok(self.value_list(&[fresh, self.value_pair_second(value)]))
            }
            TyKind::Ref(_, _, _) => Ok(value.clone()),
            TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_) => Ok(value.clone()),
            other => {
                Err(self
                    .unsupported_result(span, format!("unsupported type {other:?} during dangle")))
            }
        }
    }

    fn spec_expr_to_bool(
        &self,
        state: &State,
        expr: &Expr,
        resolved: &ResolvedExprEnv,
    ) -> Result<BoolExpr, VerificationResult> {
        match expr {
            Expr::Bool(value) => Ok(BoolExpr::Const(*value)),
            _ => Ok(BoolExpr::Value(
                self.spec_expr_to_value(state, expr, resolved)?,
            )),
        }
    }

    fn spec_expr_to_value(
        &self,
        state: &State,
        expr: &Expr,
        resolved: &ResolvedExprEnv,
    ) -> Result<Datatype, VerificationResult> {
        match expr {
            Expr::Bool(value) => Ok(self.value_bool(*value)),
            Expr::Int(value) => Ok(self.value_int(*value)),
            Expr::Var(name) if resolved.spec_vars.contains(name) => {
                self.function_spec_vars.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            Expr::Var(name) => {
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
            Expr::Bind(name) => self.function_spec_vars.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.control_span(state.ctrl),
                    format!("missing spec binding `{name}`"),
                )
            }),
            Expr::Prophecy(name) => {
                let Some(local) = resolved.prophecies.get(name) else {
                    return Err(self.unsupported_result(
                        self.control_span(state.ctrl),
                        format!("missing prophecy binding `{name}`"),
                    ));
                };
                self.local_prophecy(state, *local, self.control_span(state.ctrl))
            }
            Expr::Field { base, index } => {
                let value = self.spec_expr_to_value(state, base, resolved)?;
                self.project_tuple_field(value, *index, self.control_span(state.ctrl))
            }
            Expr::Unary { op, arg } => {
                let value = self.spec_expr_to_value(state, arg, resolved)?;
                Ok(match op {
                    UnaryOp::Not => self.value_not(&value),
                    UnaryOp::Neg => self.value_neg(&value),
                })
            }
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.spec_expr_to_value(state, lhs, resolved)?;
                let rhs = self.spec_expr_to_value(state, rhs, resolved)?;
                Ok(match op {
                    BinaryOp::Eq => self.value_eqv(&lhs, &rhs),
                    BinaryOp::Ne => self.value_not(&self.value_eqv(&lhs, &rhs)),
                    BinaryOp::And => self.value_and(&lhs, &rhs),
                    BinaryOp::Or => self.value_or(&lhs, &rhs),
                    BinaryOp::Lt => self.value_lt(&lhs, &rhs),
                    BinaryOp::Le => self.value_le(&lhs, &rhs),
                    BinaryOp::Gt => self.value_gt(&lhs, &rhs),
                    BinaryOp::Ge => self.value_ge(&lhs, &rhs),
                    BinaryOp::Add => self.value_add(&lhs, &rhs),
                    BinaryOp::Sub => self.value_sub(&lhs, &rhs),
                    BinaryOp::Mul => self.value_mul(&lhs, &rhs),
                })
            }
        }
    }

    fn contract_expr_to_bool(
        &self,
        current: &HashMap<String, Datatype>,
        prophecy: &HashMap<String, Datatype>,
        spec: &HashMap<String, Datatype>,
        expr: &Expr,
    ) -> Result<BoolExpr, VerificationResult> {
        match expr {
            Expr::Bool(value) => Ok(BoolExpr::Const(*value)),
            _ => Ok(BoolExpr::Value(
                self.contract_expr_to_value(current, prophecy, spec, expr)?,
            )),
        }
    }

    fn contract_expr_to_value(
        &self,
        current: &HashMap<String, Datatype>,
        prophecy: &HashMap<String, Datatype>,
        spec: &HashMap<String, Datatype>,
        expr: &Expr,
    ) -> Result<Datatype, VerificationResult> {
        match expr {
            Expr::Bool(value) => Ok(self.value_bool(*value)),
            Expr::Int(value) => Ok(self.value_int(*value)),
            Expr::Var(name) if spec.contains_key(name) => {
                spec.get(name).cloned().ok_or_else(|| {
                    self.unsupported_result(
                        self.tcx.def_span(self.def_id),
                        format!("missing spec binding `{name}`"),
                    )
                })
            }
            Expr::Var(name) => current.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing contract binding `{name}`"),
                )
            }),
            Expr::Bind(name) => spec.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing spec binding `{name}`"),
                )
            }),
            Expr::Prophecy(name) => prophecy.get(name).cloned().ok_or_else(|| {
                self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    format!("missing prophecy binding `{name}`"),
                )
            }),
            Expr::Field { base, index } => {
                let value = self.contract_expr_to_value(current, prophecy, spec, base)?;
                self.project_tuple_field(value, *index, self.tcx.def_span(self.def_id))
            }
            Expr::Unary { op, arg } => {
                let value = self.contract_expr_to_value(current, prophecy, spec, arg)?;
                Ok(match op {
                    UnaryOp::Not => self.value_not(&value),
                    UnaryOp::Neg => self.value_neg(&value),
                })
            }
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.contract_expr_to_value(current, prophecy, spec, lhs)?;
                let rhs = self.contract_expr_to_value(current, prophecy, spec, rhs)?;
                Ok(match op {
                    BinaryOp::Eq => self.value_eqv(&lhs, &rhs),
                    BinaryOp::Ne => self.value_not(&self.value_eqv(&lhs, &rhs)),
                    BinaryOp::And => self.value_and(&lhs, &rhs),
                    BinaryOp::Or => self.value_or(&lhs, &rhs),
                    BinaryOp::Lt => self.value_lt(&lhs, &rhs),
                    BinaryOp::Le => self.value_le(&lhs, &rhs),
                    BinaryOp::Gt => self.value_gt(&lhs, &rhs),
                    BinaryOp::Ge => self.value_ge(&lhs, &rhs),
                    BinaryOp::Add => self.value_add(&lhs, &rhs),
                    BinaryOp::Sub => self.value_sub(&lhs, &rhs),
                    BinaryOp::Mul => self.value_mul(&lhs, &rhs),
                })
            }
        }
    }

    fn contract_to_bool(
        &self,
        state: &State,
        contract: &FunctionContract,
        include_result: bool,
    ) -> Result<BoolExpr, VerificationResult> {
        let env = CallEnv::for_function(self, state, contract, self.function_spec_vars.clone())?;
        if include_result {
            self.contract_expr_to_bool(&env.current, &env.prophecy, &env.spec, &contract.ens)
        } else {
            self.contract_expr_to_bool(&env.current, &env.prophecy, &env.spec, &contract.req)
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

    fn local_prophecy(
        &self,
        state: &State,
        local: Local,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        let value = state.model.get(&local).cloned().ok_or_else(|| {
            self.unsupported_result(span, format!("missing local {}", local.as_usize()))
        })?;
        let ty = self.body.local_decls[local].ty;
        match ty.kind() {
            TyKind::Ref(_, _, mutability) if mutability.is_mut() => {
                Ok(self.value_pair_second(&value))
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
        value: &Datatype,
        inner_ty: Ty<'tcx>,
        _span: Span,
    ) -> Result<Datatype, VerificationResult> {
        let final_value = self.value_pair_second(value);
        let fresh = self.fresh_for_rust_ty(inner_ty, "opaque_cur")?;
        Ok(self.value_list(&[fresh, final_value]))
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

    fn value_error(&self) -> Datatype {
        with_value_encoding(|encoding| encoding.error())
    }

    fn value_nil(&self) -> Datatype {
        with_value_encoding(|encoding| encoding.nil())
    }

    fn value_int(&self, value: i64) -> Datatype {
        with_value_encoding(|encoding| encoding.int(value))
    }

    fn value_bool(&self, value: bool) -> Datatype {
        with_value_encoding(|encoding| encoding.bool(value))
    }

    fn value_wrap_bool(&self, value: &Bool) -> Datatype {
        with_value_encoding(|encoding| encoding.wrap_bool(value))
    }

    fn value_wrap_int(&self, value: &Int) -> Datatype {
        with_value_encoding(|encoding| encoding.wrap_int(value))
    }

    fn value_list(&self, values: &[Datatype]) -> Datatype {
        with_value_encoding(|encoding| encoding.list(values))
    }

    fn value_eqv(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.eqv(lhs, rhs))
    }

    fn value_add(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.add(lhs, rhs))
    }

    fn value_sub(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.sub(lhs, rhs))
    }

    fn value_mul(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.mul(lhs, rhs))
    }

    fn value_neg(&self, value: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.neg(value))
    }

    fn value_not(&self, value: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.notv(value))
    }

    fn value_and(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.andv(lhs, rhs))
    }

    fn value_or(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.orv(lhs, rhs))
    }

    fn value_lt(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.ltv(lhs, rhs))
    }

    fn value_le(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.lev(lhs, rhs))
    }

    fn value_gt(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.gtv(lhs, rhs))
    }

    fn value_ge(&self, lhs: &Datatype, rhs: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.gev(lhs, rhs))
    }

    fn value_is_true(&self, value: &Datatype) -> Bool {
        with_value_encoding(|encoding| encoding.is_true(value))
    }

    fn value_is_error(&self, value: &Datatype) -> Bool {
        with_value_encoding(|encoding| encoding.is_error(value))
    }

    fn value_is_int(&self, value: &Datatype) -> Bool {
        with_value_encoding(|encoding| encoding.is_int(value))
    }

    fn value_int_data(&self, value: &Datatype) -> Int {
        with_value_encoding(|encoding| encoding.int_data(value))
    }

    fn value_nth(&self, value: &Datatype, index: usize) -> Datatype {
        with_value_encoding(|encoding| encoding.nth(value, index))
    }

    fn value_pair_first(&self, value: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.pair_first(value))
    }

    fn value_pair_second(&self, value: &Datatype) -> Datatype {
        with_value_encoding(|encoding| encoding.pair_second(value))
    }

    fn fresh_for_rust_ty(&self, ty: Ty<'tcx>, hint: &str) -> Result<Datatype, VerificationResult> {
        if let TyKind::Ref(_, inner, mutability) = ty.kind()
            && mutability.is_mut()
        {
            if self.ty_contains_ref(*inner) {
                return Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "nested reference types are unsupported".to_owned(),
                ));
            }
            let current = self.fresh_for_rust_ty(*inner, &format!("{hint}_cur"))?;
            let final_value = self.fresh_for_rust_ty(*inner, &format!("{hint}_fin"))?;
            return Ok(self.value_list(&[current, final_value]));
        } else if let TyKind::Ref(_, inner, _) = ty.kind() {
            if self.ty_contains_ref(*inner) {
                return Err(self.unsupported_result(
                    self.tcx.def_span(self.def_id),
                    "nested reference types are unsupported".to_owned(),
                ));
            }
            return self.fresh_for_rust_ty(*inner, hint);
        }
        match ty.kind() {
            TyKind::Bool => Ok(self.value_wrap_bool(&Bool::new_const(self.fresh_name(hint)))),
            TyKind::Int(_) | TyKind::Uint(_) => {
                Ok(self.value_wrap_int(&Int::new_const(self.fresh_name(hint))))
            }
            TyKind::Never => Ok(self.value_error()),
            TyKind::Tuple(fields) => {
                let mut items = Vec::with_capacity(fields.len());
                for (index, field) in fields.iter().enumerate() {
                    items.push(self.fresh_for_rust_ty(field, &format!("{hint}_{index}"))?);
                }
                Ok(self.value_list(&items))
            }
            other => Err(self.unsupported_result(
                self.tcx.def_span(self.def_id),
                format!("unsupported type {other:?}"),
            )),
        }
    }

    fn project_tuple_field(
        &self,
        value: Datatype,
        index: usize,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        let _ = span;
        Ok(self.value_nth(&value, index))
    }

    fn fresh_name(&self, hint: &str) -> String {
        let id = self.next_sym.get();
        self.next_sym.set(id + 1);
        format!("{hint}_{id}")
    }

    fn ty_contains_ref(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            TyKind::Ref(..) => true,
            TyKind::Tuple(fields) => fields.iter().any(|field| self.ty_contains_ref(field)),
            _ => false,
        }
    }

    fn ty_contains_mut_ref(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            TyKind::Ref(_, _, mutability) if mutability.is_mut() => true,
            TyKind::Tuple(fields) => fields.iter().any(|field| self.ty_contains_mut_ref(field)),
            _ => false,
        }
    }

    fn int_range_formula(
        &self,
        ty: Ty<'tcx>,
        value: &Datatype,
        span: Span,
    ) -> Result<Bool, VerificationResult> {
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
        Ok(bool_and(vec![
            self.value_is_int(value),
            self.value_int_data(value).ge(bounds.0),
            self.value_int_data(value).le(bounds.1),
        ]))
    }

    fn overflow_value_for_result(
        &self,
        ty: Ty<'tcx>,
        value: &Datatype,
        span: Span,
    ) -> Result<Datatype, VerificationResult> {
        let in_range = self.int_range_formula(ty, value, span)?;
        Ok(self.value_is_error(value).ite(
            &self.value_error(),
            &self.value_wrap_bool(&bool_not(in_range)),
        ))
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
        spec: HashMap<String, Datatype>,
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
            let value = self.read_operand(state, &arg.node, span)?;
            let ty = arg.node.ty(&self.body.local_decls, self.tcx);
            current.insert(name.clone(), value.clone());
            prophecy.insert(
                name.clone(),
                self.prophecy_from_typed_value(ty, &value, span)?,
            );
        }
        Ok(CallEnv {
            current,
            prophecy,
            spec,
        })
    }

    fn instantiate_contract_spec_vars(&self, names: &[String]) -> HashMap<String, Datatype> {
        let mut spec = HashMap::new();
        for name in names {
            let value = with_value_encoding(|encoding| encoding.fresh(&self.fresh_name(name)));
            spec.insert(name.clone(), value);
        }
        spec
    }

    fn prophecy_from_typed_value(
        &self,
        ty: Ty<'tcx>,
        value: &Datatype,
        _span: Span,
    ) -> Result<Datatype, VerificationResult> {
        match ty.kind() {
            TyKind::Ref(_, _, mutability) if mutability.is_mut() => {
                Ok(self.value_pair_second(value))
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
    current: HashMap<String, Datatype>,
    prophecy: HashMap<String, Datatype>,
    spec: HashMap<String, Datatype>,
}

impl CallEnv {
    fn for_function<'tcx>(
        verifier: &Verifier<'tcx>,
        state: &State,
        contract: &FunctionContract,
        spec: HashMap<String, Datatype>,
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
        Ok(Self {
            current,
            prophecy,
            spec,
        })
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

fn with_value_encoding<T>(f: impl FnOnce(&ValueEncoding) -> T) -> T {
    VALUE_ENCODING.with(|encoding| f(encoding))
}

fn instantiate_spec_vars(next_sym: &Cell<usize>, names: &[String]) -> HashMap<String, Datatype> {
    let mut spec = HashMap::new();
    for name in names {
        let index = next_sym.get();
        next_sym.set(index + 1);
        let symbol = format!("spec_{name}_{index}");
        let value = with_value_encoding(|encoding| encoding.fresh(&symbol));
        spec.insert(name.clone(), value);
    }
    spec
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

fn span_text(tcx: TyCtxt<'_>, span: Span) -> String {
    tcx.sess.source_map().span_to_diagnostic_string(span)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_encoding_eqv_handles_lists() {
        reset_solver();
        with_value_encoding(|encoding| {
            let list1 = encoding.list(&[encoding.int(1), encoding.bool(true)]);
            let list2 = encoding.list(&[encoding.int(1), encoding.bool(true)]);
            let list3 = encoding.list(&[encoding.int(2), encoding.bool(true)]);

            with_solver(|solver| {
                solver.assert(encoding.is_true(&encoding.eqv(&list1, &list2)));
                assert_eq!(solver.check(), SatResult::Sat);
                solver.reset();

                solver.assert(encoding.is_true(&encoding.eqv(&list1, &list3)));
                assert_eq!(solver.check(), SatResult::Unsat);
            });
        });
    }

    #[test]
    fn value_encoding_add_propagates_error() {
        reset_solver();
        with_value_encoding(|encoding| {
            let sum = encoding.add(&encoding.error(), &encoding.int(1));
            with_solver(|solver| {
                solver.assert(encoding.is_error(&sum));
                assert_eq!(solver.check(), SatResult::Sat);
            });
        });
    }

    #[test]
    fn value_encoding_is_true_only_accepts_true_bool() {
        reset_solver();
        with_value_encoding(|encoding| {
            with_solver(|solver| {
                solver.assert(encoding.is_true(&encoding.bool(true)));
                assert_eq!(solver.check(), SatResult::Sat);
                solver.reset();

                solver.assert(encoding.is_true(&encoding.bool(false)));
                assert_eq!(solver.check(), SatResult::Unsat);
                solver.reset();

                solver.assert(encoding.is_true(&encoding.error()));
                assert_eq!(solver.check(), SatResult::Unsat);
            });
        });
    }
}
