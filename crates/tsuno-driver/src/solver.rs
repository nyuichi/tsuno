//! Verification solver backend that owns Z3 state and value encoding.

use std::cell::RefCell;
use std::sync::Once;

use crate::spec::{BinaryOp, EnumDef, RustTyKey, SpecTy, UnaryOp};
use crate::value::{
    CompositeCtorView, DirectCtorFields, IntValueBinaryOp, IntValuePredicateOp, IntValueResult,
    OptionCtorKind, SymValue, ValueEncoder,
};
use z3::ast::{Bool, Int};
use z3::{SatResult, Solver as Z3Solver, Sort};

const SOLVER_TIMEOUT_MS: u32 = 1_000;

static Z3_INIT: Once = Once::new();

thread_local! {
    static Z3_SOLVER: RefCell<Z3Solver> = RefCell::new(build_z3_solver());
}

pub(crate) struct Solver {
    values: ValueEncoder,
}

impl Solver {
    pub(crate) fn new(pointer_bits: u64) -> Self {
        rebuild_z3_solver();
        Self {
            values: ValueEncoder::new(pointer_bits),
        }
    }

    pub(crate) fn reset(&self) {
        reset_z3_solver();
        self.values.reset_solver_state();
    }

    pub(crate) fn register_enum_def(&self, def: EnumDef) {
        self.values.register_enum_def(def);
    }

    pub(crate) fn check_assumptions(&self, assumptions: &[Bool]) -> SatResult {
        with_z3_solver(|solver| solver.check_assumptions(assumptions))
    }

    pub(crate) fn bool_value(&self, value: bool) -> SymValue {
        self.values.bool_value(value)
    }

    pub(crate) fn bool_term(&self, value: &SymValue) -> Bool {
        self.values.bool_term(value)
    }

    pub(crate) fn int_value(&self, value: i64) -> SymValue {
        self.values.int_value(value)
    }

    pub(crate) fn int_term(&self, value: &SymValue) -> Int {
        self.values.int_term(value)
    }

    pub(crate) fn decimal_int_value(&self, digits: &str) -> Result<SymValue, String> {
        self.values.decimal_int_value(digits)
    }

    pub(crate) fn rust_ty_value(&self, key: &RustTyKey) -> SymValue {
        with_z3_solver(|solver| self.values.rust_ty_value(key, solver))
    }

    pub(crate) fn seq_literal_value(&self, items: &[SymValue]) -> SymValue {
        self.values.seq_literal_value(items)
    }

    pub(crate) fn seq_len_int(&self, value: &SymValue) -> Result<Int, String> {
        self.values.seq_len_int(value)
    }

    pub(crate) fn seq_nth_value(&self, value: &SymValue, index: &Int) -> Result<SymValue, String> {
        self.values.seq_nth_value(value, index)
    }

    pub(crate) fn nat_to_int_term(&self, value: &SymValue) -> Result<Int, String> {
        with_z3_solver(|solver| self.values.nat_to_int_term(value, solver))
    }

    pub(crate) fn int_to_nat_value(&self, value: &Int) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.int_to_nat_value(value, solver))
    }

    pub(crate) fn concrete_nat_value(&self, n: u64) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.concrete_nat_value(n, solver))
    }

    pub(crate) fn sort_for_ty(&self, ty: &SpecTy) -> Result<Sort, String> {
        with_z3_solver(|solver| self.values.sort_for_ty(ty, solver))
    }

    pub(crate) fn eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<Bool, String> {
        with_z3_solver(|solver| self.values.eq_for_spec_ty(ty, lhs, rhs, solver))
    }

    pub(crate) fn lower_binary_predicate(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<Option<Bool>, String> {
        with_z3_solver(|solver| {
            self.values
                .lower_binary_predicate(op, lhs_ty, lhs, rhs, solver)
        })
    }

    pub(crate) fn lower_unary_value(&self, op: UnaryOp, value: &SymValue) -> SymValue {
        self.values.lower_unary_value(op, value)
    }

    pub(crate) fn lower_bool_not_value(&self, value: &SymValue) -> SymValue {
        self.values.lower_bool_not_value(value)
    }

    pub(crate) fn lower_int_neg_value(&self, value: &SymValue) -> IntValueResult {
        self.values.lower_int_neg_value(value)
    }

    pub(crate) fn lower_int_binary_value(
        &self,
        op: IntValueBinaryOp,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> IntValueResult {
        self.values.lower_int_binary_value(op, lhs, rhs)
    }

    pub(crate) fn lower_int_predicate_value(
        &self,
        op: IntValuePredicateOp,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> SymValue {
        self.values.lower_int_predicate_value(op, lhs, rhs)
    }

    pub(crate) fn lower_eq_value(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        negated: bool,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.lower_eq_value(ty, lhs, rhs, negated, solver))
    }

    pub(crate) fn lower_binary_value(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.lower_binary_value(op, lhs_ty, lhs, rhs, solver))
    }

    pub(crate) fn construct_composite(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.construct_composite(ty, fields, solver))
    }

    pub(crate) fn construct_composite_ctor(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| {
            self.values
                .construct_composite_ctor(ty, ctor_index, fields, solver)
        })
    }

    pub(crate) fn construct_option_none(&self, inner: SpecTy) -> Result<SymValue, String> {
        self.values.construct_option_none(inner)
    }

    pub(crate) fn construct_option_some(
        &self,
        inner: SpecTy,
        value: SymValue,
    ) -> Result<SymValue, String> {
        self.values.construct_option_some(inner, value)
    }

    pub(crate) fn option_ctor_kind(
        &self,
        ctor_index: usize,
    ) -> Result<Option<OptionCtorKind>, String> {
        self.values.option_ctor_kind(ctor_index)
    }

    pub(crate) fn checked_result_tuple_value(
        &self,
        result_ty: SpecTy,
        result_value: SymValue,
        overflow_value: SymValue,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| {
            self.values
                .checked_result_tuple_value(result_ty, result_value, overflow_value, solver)
        })
    }

    pub(crate) fn fresh_for_spec_ty(
        &self,
        ty: &SpecTy,
        hint: &str,
        fresh_name: &mut impl FnMut(&str) -> String,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.fresh_for_spec_ty(ty, hint, solver, fresh_name))
    }

    pub(crate) fn project_field(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.values.project_field(ty, value, index, solver))
    }

    pub(crate) fn project_composite_ctor_field_for_ty(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| {
            self.values
                .project_composite_ctor_field_for_ty(ty, ctor_index, value, index, solver)
        })
    }

    pub(crate) fn composite_ctor_view_for_ty(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
    ) -> Result<CompositeCtorView, String> {
        with_z3_solver(|solver| {
            self.values
                .composite_ctor_view_for_ty(ty, ctor_index, value, solver)
        })
    }

    pub(crate) fn direct_composite_fields_for_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Option<Vec<SymValue>>, String> {
        with_z3_solver(|solver| {
            self.values
                .direct_composite_fields_for_ty(ty, value, solver)
        })
    }

    pub(crate) fn direct_composite_ctor_fields_for_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Option<DirectCtorFields>, String> {
        with_z3_solver(|solver| {
            self.values
                .direct_composite_ctor_fields_for_ty(ty, value, solver)
        })
    }

    pub(crate) fn tag_formula_for_ty(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
    ) -> Result<Bool, String> {
        with_z3_solver(|solver| {
            self.values
                .tag_formula_for_ty(ty, ctor_index, value, solver)
        })
    }

    pub(crate) fn ground_ctor_index(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Option<usize>, String> {
        with_z3_solver(|solver| self.values.ground_ctor_index(ty, value, solver))
    }

    pub(crate) fn named_invariant_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Bool, String> {
        with_z3_solver(|solver| self.values.named_invariant_formula(ty, value, solver))
    }

    pub(crate) fn int_bounds(&self, ty: &SpecTy) -> Result<Option<(Int, Int)>, String> {
        self.values.int_bounds(ty)
    }

    pub(crate) fn scalar_int_value(&self, value: &Int) -> SymValue {
        self.values.scalar_int_value(value)
    }

    pub(crate) fn overflow_value_for_in_range(&self, in_range: Bool) -> SymValue {
        self.values.overflow_value_for_in_range(in_range)
    }

    pub(crate) fn offset_int_value(&self, base: &SymValue, offset: u64) -> SymValue {
        self.values.offset_int_value(base, offset)
    }
}

fn init_z3() {
    Z3_INIT.call_once(|| {
        z3::set_global_param("model", "true");
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");
    });
}

fn build_z3_solver() -> Z3Solver {
    init_z3();
    let solver = Z3Solver::new();
    let mut params = z3::Params::new();
    params.set_u32("timeout", SOLVER_TIMEOUT_MS);
    solver.set_params(&params);
    solver
}

pub(crate) fn rebuild_z3_solver() {
    Z3_SOLVER.with(|solver| {
        *solver.borrow_mut() = build_z3_solver();
    });
}

fn reset_z3_solver() {
    with_z3_solver(|solver| {
        solver.reset();
    });
}

pub(crate) fn with_z3_solver<T>(f: impl FnOnce(&Z3Solver) -> T) -> T {
    Z3_SOLVER.with(|solver| f(&solver.borrow()))
}
