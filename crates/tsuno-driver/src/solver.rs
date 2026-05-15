//! Verification solver backend for Z3 state, spec values, constructors, and invariants.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::Once;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use crate::spec::{
    BinaryOp, EnumDef, RustTyKey, SpecTy, StructDef, UnaryOp, option_spec_ty, ptr_spec_ty,
};
use z3::ast::{self, Ast, BV, Bool, Dynamic, Int, Seq as Z3Seq};
use z3::{
    Config, Context, DeclKind, FuncDecl, Pattern, RecFuncDecl, SatResult, Solver as Z3Solver, Sort,
    SortKind, Symbol,
};

const SOLVER_TIMEOUT_MS: u32 = 1_000;

static Z3_INIT: Once = Once::new();

thread_local! {
    static Z3_SOLVER: RefCell<Z3Solver> = RefCell::new(build_z3_solver());
}

/*
Value encoding overview

All spec values inhabit one uninterpreted Z3 sort:

  value

Primitive values still use dedicated boxing/unboxing symbols:

  boolbox : Bool -> value
  bool    : value -> Bool
  intbox  : Int -> value
  int     : value -> Int

Important: we intentionally do not assert quantified primitive reboxing axioms
such as

  forall v: value. boolbox(bool(v)) = v
  forall v: value. intbox(int(v)) = v

Those axioms made the shared `value` sort too strong and could collapse
distinct representations. Instead, `bool_term` / `int_term` only unwrap
syntactically obvious boxed terms:

  bool_term(boolbox(b)) = b
  int_term(intbox(i)) = i

For an opaque `v: value`, `bool(v)` and `int(v)` remain uninterpreted.

Composite values are arranged like constructor families.

- Structural composites (`Tuple`, `Struct`, `Ref<T>`, `Mut<T>`) get fresh
  per-type constructor/tag/projection symbols, but unlike named spec types we
  do not assert general `forall` laws for them, e.g.

    forall x0 .. xn-1. ctortag<family>(mk_<name>(x0, .., xn-1)) = TAG_<name>
    forall x0 .. xn-1. ctorinv_<name>_<i>(mk_<name>(x0, .., xn-1)) = xi

  We only exploit those equalities syntactically when the term already is a
  visible constructor application.
- Enum spec types (`SpecTy::Enum`, i.e. ghost enums such as `List<T>`) reuse
  one nominal constructor family across all instantiations of the same enum
  declaration. Type arguments are enforced through per-instantiation invariant
  predicates.

For a constructor family whose sanitized constructor name is `<name>`, the
backend creates:

  mk_<name>          : value^n -> value
  ctortag<family>    : value -> Int
  ctorinv_<name>_<i> : value -> value
  TAG_<name>         : Int literal unique to the constructor

For named spec types only, the backend asserts:

  forall x0 .. xn-1. ctortag<family>(mk_<name>(x0, .., xn-1)) = TAG_<name>
    pattern: mk_<name>(x0, .., xn-1)

  forall x0 .. xn-1. ctorinv_<name>_<i>(mk_<name>(x0, .., xn-1)) = xi
    pattern: mk_<name>(x0, .., xn-1)

If a named family has exactly one non-empty constructor, it also gets the
eta-style axiom:

  forall v: value.
    mk_<name>(ctorinv_<name>_0(v), .., ctorinv_<name>_n(v)) = v

Enum spec types also get a per-instantiation invariant predicate:

  inv_<name<args>> : value -> Bool

The asserted invariant axioms have two directions.

Constructor introduction:

  forall x0 .. xn-1.
    field_inv_0(x0) && .. && field_inv_n(xn-1)
      => inv_<name<args>>(mk_<name>(x0, .., xn-1))

Invariant elimination:

  forall v: value.
    inv_<name<args>>(v)
      => OR_over_ctors(
           ctortag<family>(v) = TAG_<name_k>
           && field_inv_0(ctorinv_<name_k>_0(v))
           && ..
         )

For structural composites we do not assert those quantified constructor laws.
Instead, a few operations perform syntactic reasoning when the term is already a
constructor application:

  project_composite_field(mk_<name>(...), i)  ==> syntactically returns arg_i
  tag_formula(mk_<name>(...), k)              ==> true/false syntactically

If the value is opaque, those operations fall back to uninterpreted projection
or tag terms; there is no global eta/extensionality axiom for tuples, refs, or
plain structs.

Pure functions are encoded in `engine.rs` on top of these symbols using
`RecFuncDecl`. This file owns the verification solver backend: Z3 solver
lifecycle, value-level constructor/tag/invariant encoding, and built-in value
conversions that those recursive definitions refer to.
*/

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SymValue {
    ast: Dynamic,
}

impl SymValue {
    pub(crate) fn new(ast: Dynamic) -> Self {
        Self { ast }
    }

    pub(crate) fn dynamic(&self) -> &Dynamic {
        &self.ast
    }

    pub(crate) fn ast(&self) -> &dyn Ast {
        &self.ast
    }
}

#[derive(Debug)]
struct TypeEncoding {
    kind: TypeEncodingKind,
    sort: Sort,
}

#[derive(Debug)]
enum TypeEncodingKind {
    Bool,
    Int,
    Opaque,
    Seq,
    Composite(Rc<CompositeEncoding>),
}

#[derive(Debug)]
struct PrimitiveEncoding {
    boxed: FuncDecl,
    unboxed: FuncDecl,
}

#[derive(Debug)]
struct CompositeEncoding {
    tag_function: FuncDecl,
    constructors: Vec<Rc<ConstructorEncoding>>,
    invariant: Option<Rc<FuncDecl>>,
}

#[derive(Debug)]
struct EnumFamilyEncoding {
    tag_function_name: String,
    constructors: Vec<Rc<EnumFamilyCtorEncoding>>,
}

#[derive(Debug)]
struct EnumFamilyCtorEncoding {
    symbol_name: String,
    inverse_names: Vec<String>,
    tag_value: u32,
}

struct BuiltinNatDecls {
    nat_to_int: RecFuncDecl,
    int_to_nat: RecFuncDecl,
}

pub(crate) struct DirectCtorFields {
    pub(crate) ctor_index: usize,
    pub(crate) fields: Vec<(SpecTy, SymValue)>,
}

pub(crate) struct CompositeCtorView {
    pub(crate) tag: Bool,
    pub(crate) fields: Vec<(SpecTy, SymValue)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OptionCtorKind {
    None,
    Some,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IntValueBinaryOp {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IntValuePredicateOp {
    Lt,
    Le,
    Gt,
    Ge,
}

pub(crate) struct IntValueResult {
    pub(crate) term: Int,
    pub(crate) value: SymValue,
}

impl CompositeEncoding {
    fn single_constructor(&self) -> Result<&ConstructorEncoding, String> {
        match self.constructors.as_slice() {
            [ctor] => Ok(ctor.as_ref()),
            ctors => Err(format!(
                "expected exactly one constructor, found {}",
                ctors.len()
            )),
        }
    }
}

#[derive(Debug)]
struct ConstructorEncoding {
    name: String,
    symbol: FuncDecl,
    fields: Vec<FieldEncoding>,
    tag: Int,
}

#[derive(Debug)]
struct FieldEncoding {
    inverse: FuncDecl,
    ty: SpecTy,
}

type CtorFields = Vec<(String, SpecTy)>;
type CtorSpecs = Vec<(String, CtorFields)>;

pub(crate) struct Solver {
    pointer_width_bits: u64,
    value_sort: Sort,
    seq_value_sort: Sort,
    bool_encoding: Rc<PrimitiveEncoding>,
    int_encoding: Rc<PrimitiveEncoding>,
    primitive_axioms_asserted: Cell<bool>,
    next_subtype_id: Cell<u32>,
    next_ctor_tag: Cell<u32>,
    enum_defs: RefCell<BTreeMap<String, EnumDef>>,
    struct_defs: RefCell<BTreeMap<String, StructDef>>,
    enum_family_encodings: RefCell<BTreeMap<String, Rc<EnumFamilyEncoding>>>,
    type_encodings: RefCell<BTreeMap<SpecTy, Rc<TypeEncoding>>>,
    asserted_type_axioms: RefCell<BTreeSet<SpecTy>>,
    rust_ty_values: RefCell<BTreeMap<RustTyKey, SymValue>>,
    asserted_rust_ty_distinct: RefCell<BTreeSet<(RustTyKey, RustTyKey)>>,
    builtin_nat_decls: RefCell<Option<Rc<BuiltinNatDecls>>>,
    pure_fn_decls: RefCell<BTreeMap<String, RecFuncDecl>>,
}

impl Solver {
    pub(crate) fn new(pointer_width_bits: u64) -> Self {
        rebuild_z3_solver();
        let value_sort = Sort::uninterpreted(Symbol::String("value".to_owned()));
        let seq_value_sort = Sort::seq(&value_sort);
        let bool_encoding = Rc::new(PrimitiveEncoding {
            boxed: FuncDecl::new("(boolbox)", &[&Sort::bool()], &value_sort),
            unboxed: FuncDecl::new("(bool)", &[&value_sort], &Sort::bool()),
        });
        let int_encoding = Rc::new(PrimitiveEncoding {
            boxed: FuncDecl::new("(intbox)", &[&Sort::int()], &value_sort),
            unboxed: FuncDecl::new("(int)", &[&value_sort], &Sort::int()),
        });

        Self {
            pointer_width_bits,
            value_sort,
            seq_value_sort,
            bool_encoding,
            int_encoding,
            primitive_axioms_asserted: Cell::new(false),
            next_subtype_id: Cell::new(0),
            next_ctor_tag: Cell::new(0),
            enum_defs: RefCell::new(BTreeMap::new()),
            struct_defs: RefCell::new(BTreeMap::new()),
            enum_family_encodings: RefCell::new(BTreeMap::new()),
            type_encodings: RefCell::new(BTreeMap::new()),
            asserted_type_axioms: RefCell::new(BTreeSet::new()),
            rust_ty_values: RefCell::new(BTreeMap::new()),
            asserted_rust_ty_distinct: RefCell::new(BTreeSet::new()),
            builtin_nat_decls: RefCell::new(None),
            pure_fn_decls: RefCell::new(BTreeMap::new()),
        }
    }

    pub(crate) fn reset(&self) {
        reset_z3_solver();
        self.primitive_axioms_asserted.set(false);
        self.asserted_type_axioms.borrow_mut().clear();
        self.asserted_rust_ty_distinct.borrow_mut().clear();
        self.builtin_nat_decls.replace(None);
    }

    pub(crate) fn register_enum_def(&self, def: EnumDef) {
        self.enum_defs.borrow_mut().insert(def.name.clone(), def);
    }

    pub(crate) fn register_struct_def(&self, def: StructDef) {
        self.struct_defs.borrow_mut().insert(def.name.clone(), def);
    }

    pub(crate) fn enum_ctor_index(
        &self,
        enum_name: &str,
        ctor_name: &str,
    ) -> Result<usize, String> {
        let enum_defs = self.enum_defs.borrow();
        let enum_def = enum_defs
            .get(enum_name)
            .ok_or_else(|| format!("unknown spec enum `{enum_name}`"))?;
        enum_def
            .ctor(ctor_name)
            .map(|(index, _)| index)
            .ok_or_else(|| format!("unknown constructor `{enum_name}::{ctor_name}`"))
    }

    pub(crate) fn option_ctor_kind(
        &self,
        ctor_index: usize,
    ) -> Result<Option<OptionCtorKind>, String> {
        if ctor_index == self.enum_ctor_index("Option", "None")? {
            return Ok(Some(OptionCtorKind::None));
        }
        if ctor_index == self.enum_ctor_index("Option", "Some")? {
            return Ok(Some(OptionCtorKind::Some));
        }
        Ok(None)
    }

    pub(crate) fn named_invariant_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Bool, String> {
        with_z3_solver(|solver| self.named_invariant_formula_with_z3(ty, value, solver))
    }

    pub(crate) fn nat_to_int_term(&self, value: &SymValue) -> Result<Int, String> {
        with_z3_solver(|solver| self.nat_to_int_term_with_z3(value, solver))
    }

    pub(crate) fn int_to_nat_value(&self, value: &Int) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.int_to_nat_value_with_z3(value, solver))
    }

    pub(crate) fn concrete_nat_value(&self, n: u64) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.concrete_nat_value_with_z3(n, solver))
    }

    pub(crate) fn rust_ty_value(&self, key: &RustTyKey) -> SymValue {
        with_z3_solver(|solver| self.rust_ty_value_with_z3(key, solver))
    }

    pub(crate) fn eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<Bool, String> {
        with_z3_solver(|solver| self.eq_for_spec_ty_with_z3(ty, lhs, rhs, solver))
    }

    pub(crate) fn lower_eq_value(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        negated: bool,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.lower_eq_value_with_z3(ty, lhs, rhs, negated, solver))
    }

    pub(crate) fn lower_binary_value(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.lower_binary_value_with_z3(op, lhs_ty, lhs, rhs, solver))
    }

    pub(crate) fn lower_binary_predicate(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<Option<Bool>, String> {
        with_z3_solver(|solver| self.lower_binary_predicate_with_z3(op, lhs_ty, lhs, rhs, solver))
    }

    pub(crate) fn construct_composite(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.construct_composite_with_z3(ty, fields, solver))
    }

    pub(crate) fn construct_composite_ctor(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| {
            self.construct_composite_ctor_with_z3(ty, ctor_index, fields, solver)
        })
    }

    pub(crate) fn checked_result_tuple_value(
        &self,
        result_ty: SpecTy,
        result_value: SymValue,
        overflow_value: SymValue,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| {
            self.checked_result_tuple_value_with_z3(result_ty, result_value, overflow_value, solver)
        })
    }

    pub(crate) fn fresh_for_spec_ty(
        &self,
        ty: &SpecTy,
        hint: &str,
        fresh_name: &mut impl FnMut(&str) -> String,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.fresh_for_spec_ty_with_z3(ty, hint, solver, fresh_name))
    }

    pub(crate) fn project_field(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| self.project_field_with_z3(ty, value, index, solver))
    }

    pub(crate) fn project_composite_ctor_field_for_ty(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        with_z3_solver(|solver| {
            self.project_composite_ctor_field_for_ty_with_z3(ty, ctor_index, value, index, solver)
        })
    }

    pub(crate) fn composite_ctor_view_for_ty(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
    ) -> Result<CompositeCtorView, String> {
        with_z3_solver(|solver| {
            self.composite_ctor_view_for_ty_with_z3(ty, ctor_index, value, solver)
        })
    }

    pub(crate) fn direct_composite_ctor_fields_for_ty(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Option<DirectCtorFields>, String> {
        with_z3_solver(|solver| self.direct_composite_ctor_fields_for_ty_with_z3(ty, value, solver))
    }

    pub(crate) fn tag_formula_for_ty(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
    ) -> Result<Bool, String> {
        with_z3_solver(|solver| self.tag_formula_for_ty_with_z3(ty, ctor_index, value, solver))
    }

    pub(crate) fn ground_ctor_index(
        &self,
        ty: &SpecTy,
        value: &SymValue,
    ) -> Result<Option<usize>, String> {
        with_z3_solver(|solver| self.ground_ctor_index_with_z3(ty, value, solver))
    }

    pub(crate) fn check_assumptions(&self, assumptions: &[Bool]) -> SatResult {
        with_z3_solver(|solver| solver.check_assumptions(assumptions))
    }

    pub(crate) fn bool_marker(&self, name: impl Into<Symbol>) -> Bool {
        Bool::new_const(name)
    }

    pub(crate) fn simplify_bool(value: &Bool) -> Bool {
        value.simplify()
    }

    pub(crate) fn simplify_int(value: &Int) -> Int {
        value.simplify()
    }

    pub(crate) fn bool_contains_marker(expr: &Bool, marker: &str) -> bool {
        if expr.is_const() {
            return expr.decl().name() == marker;
        }
        expr.children().into_iter().any(|child| {
            child
                .as_bool()
                .filter(|_| child.sort_kind() == SortKind::Bool)
                .map(|child| Self::bool_contains_marker(&child, marker))
                .unwrap_or(false)
        })
    }

    pub(crate) fn declare_pure_fn(
        &self,
        name: &str,
        param_tys: &[SpecTy],
        result_ty: &SpecTy,
    ) -> Result<(), String> {
        with_z3_solver(|solver| {
            let domain_sorts = param_tys
                .iter()
                .map(|ty| self.sort_for_ty_with_z3(ty, solver))
                .collect::<Result<Vec<_>, _>>()?;
            let domain_refs = domain_sorts.iter().collect::<Vec<_>>();
            let result_sort = self.sort_for_ty_with_z3(result_ty, solver)?;
            let decl = RecFuncDecl::new(format!("pure_fn_{name}"), &domain_refs, &result_sort);
            let inserted = self
                .pure_fn_decls
                .borrow_mut()
                .insert(name.to_owned(), decl)
                .is_none();
            assert!(inserted, "duplicate pure function decl `{name}`");
            Ok(())
        })
    }

    pub(crate) fn pure_fn_params(
        &self,
        func: &str,
        params: &[(String, SpecTy)],
        fresh_name: &mut impl FnMut(&str) -> String,
    ) -> Result<Vec<(String, SymValue)>, String> {
        with_z3_solver(|solver| {
            let mut values = Vec::with_capacity(params.len());
            for (name, ty) in params {
                let sort = self.sort_for_ty_with_z3(ty, solver)?;
                let value = SymValue::new(Dynamic::new_const(
                    fresh_name(&format!("pure_{func}_{name}")),
                    &sort,
                ));
                values.push((name.clone(), value));
            }
            Ok(values)
        })
    }

    pub(crate) fn define_pure_fn(
        &self,
        name: &str,
        args: &[SymValue],
        body: &SymValue,
    ) -> Result<(), String> {
        let decls = self.pure_fn_decls.borrow();
        let decl = decls
            .get(name)
            .ok_or_else(|| format!("unknown pure function `{name}`"))?;
        let args = args.iter().map(SymValue::ast).collect::<Vec<_>>();
        decl.add_def(&args, body.dynamic());
        Ok(())
    }

    pub(crate) fn apply_pure_fn(
        &self,
        name: &str,
        args: &[SymValue],
    ) -> Result<Option<SymValue>, String> {
        let decls = self.pure_fn_decls.borrow();
        let Some(decl) = decls.get(name) else {
            return Ok(None);
        };
        let args = args.iter().map(SymValue::ast).collect::<Vec<_>>();
        Ok(Some(SymValue::new(decl.apply(&args))))
    }

    #[cfg(test)]
    pub(crate) fn value_sort(&self) -> &Sort {
        &self.value_sort
    }

    fn type_encoding(&self, ty: &SpecTy, solver: &Z3Solver) -> Result<Rc<TypeEncoding>, String> {
        self.ensure_primitive_axioms(solver);
        let cached = { self.type_encodings.borrow().get(ty).cloned() };
        if let Some(encoding) = cached {
            if !self.asserted_type_axioms.borrow().contains(ty) {
                self.asserted_type_axioms.borrow_mut().insert(ty.clone());
                self.assert_type_axioms(ty, &encoding, solver)?;
            }
            return Ok(encoding);
        }
        let encoding = self.build_type_encoding(ty)?;
        self.type_encodings
            .borrow_mut()
            .insert(ty.clone(), encoding.clone());
        self.asserted_type_axioms.borrow_mut().insert(ty.clone());
        self.assert_type_axioms(ty, &encoding, solver)?;
        Ok(encoding)
    }

    fn sort_for_ty_with_z3(&self, ty: &SpecTy, solver: &Z3Solver) -> Result<Sort, String> {
        Ok(self.type_encoding(ty, solver)?.sort.clone())
    }

    fn composite_encoding(
        &self,
        ty: &SpecTy,
        solver: &Z3Solver,
    ) -> Result<Rc<CompositeEncoding>, String> {
        let encoding = self.type_encoding(ty, solver)?;
        match &encoding.kind {
            TypeEncodingKind::Composite(encoding) => Ok(encoding.clone()),
            _ => Err(format!("expected composite-backed spec type, found {ty:?}")),
        }
    }

    fn named_invariant(
        &self,
        ty: &SpecTy,
        solver: &Z3Solver,
    ) -> Result<Option<Rc<FuncDecl>>, String> {
        let composite = self.composite_encoding(ty, solver)?;
        Ok(composite.invariant.clone())
    }

    fn named_invariant_formula_with_z3(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Bool, String> {
        let invariant = self
            .named_invariant(ty, solver)?
            .ok_or_else(|| format!("missing named invariant for {ty:?}"))?;
        Ok(invariant
            .apply(&[value.ast()])
            .as_bool()
            .expect("named invariant predicate"))
    }

    pub(crate) fn wrap_bool(&self, value: &Bool) -> SymValue {
        SymValue::new(self.bool_encoding.boxed.apply(&[value]))
    }

    pub(crate) fn wrap_int(&self, value: &Int) -> SymValue {
        SymValue::new(self.int_encoding.boxed.apply(&[value]))
    }

    pub(crate) fn overflow_value_for_in_range(&self, in_range: Bool) -> SymValue {
        self.wrap_bool(&in_range.not())
    }

    pub(crate) fn scalar_int_value(&self, value: &Int) -> SymValue {
        self.wrap_int(value)
    }

    pub(crate) fn offset_int_value(&self, base: &SymValue, offset: u64) -> SymValue {
        if offset == 0 {
            return base.clone();
        }
        self.wrap_int(&(self.int_term(base) + Int::from_u64(offset)))
    }

    pub(crate) fn empty_seq_value(&self) -> SymValue {
        SymValue::new(Dynamic::from(Z3Seq::empty(&self.value_sort)))
    }

    pub(crate) fn seq_literal_value(&self, items: &[SymValue]) -> SymValue {
        if items.is_empty() {
            return self.empty_seq_value();
        }
        let parts = items
            .iter()
            .map(|item| Z3Seq::unit(item.dynamic()))
            .collect::<Vec<_>>();
        let part_refs = parts.iter().collect::<Vec<_>>();
        SymValue::new(Dynamic::from(Z3Seq::concat(&part_refs)))
    }

    pub(crate) fn seq_term(&self, value: &SymValue) -> Result<Z3Seq, String> {
        value
            .dynamic()
            .as_seq()
            .ok_or_else(|| "expected sequence-backed symbolic value".to_owned())
    }

    pub(crate) fn seq_len_int(&self, value: &SymValue) -> Result<Int, String> {
        if let Some(length) = Self::ground_seq_len(value.dynamic()) {
            return Ok(Int::from_u64(length as u64));
        }
        Ok(self.seq_term(value)?.length())
    }

    pub(crate) fn seq_nth_value(&self, value: &SymValue, index: &Int) -> Result<SymValue, String> {
        if let Some(index) = index.as_i64().filter(|index| *index >= 0)
            && let Some(item) = Self::ground_seq_nth(value.dynamic(), index as usize)
        {
            return Ok(SymValue::new(item));
        }
        Ok(SymValue::new(
            self.seq_term(value)?.nth(index.clone()).simplify(),
        ))
    }

    fn nat_to_int_term_with_z3(&self, value: &SymValue, solver: &Z3Solver) -> Result<Int, String> {
        if let Some(n) = self.try_concrete_nat_usize(value, solver)? {
            return Ok(Int::from_u64(n));
        }
        let decls = self.builtin_nat_decls(solver)?;
        decls
            .nat_to_int
            .apply(&[value.ast()])
            .as_int()
            .ok_or_else(|| "builtin_nat_to_int must return Int".to_owned())
    }

    fn int_to_nat_value_with_z3(&self, value: &Int, solver: &Z3Solver) -> Result<SymValue, String> {
        let decls = self.builtin_nat_decls(solver)?;
        Ok(SymValue::new(decls.int_to_nat.apply(&[value])))
    }

    fn concrete_nat_value_with_z3(&self, n: u64, solver: &Z3Solver) -> Result<SymValue, String> {
        let nat_ty = Self::nat_spec_ty();
        let (zero, succ) = self.nat_ctor_indices(solver)?;
        let mut value = self.construct_composite_ctor_with_z3(&nat_ty, zero, &[], solver)?;
        for _ in 0..n {
            value = self.construct_composite_ctor_with_z3(&nat_ty, succ, &[value], solver)?;
        }
        Ok(value)
    }

    fn ground_seq_nth(ast: &Dynamic, index: usize) -> Option<Dynamic> {
        match ast.decl().kind() {
            DeclKind::SEQ_UNIT => ast.children().first().cloned().filter(|_| index == 0),
            DeclKind::SEQ_EMPTY => None,
            DeclKind::SEQ_CONCAT => {
                let mut remaining = index;
                for child in ast.children() {
                    let child_len = Self::ground_seq_len(&child)?;
                    if remaining < child_len {
                        return Self::ground_seq_nth(&child, remaining);
                    }
                    remaining -= child_len;
                }
                None
            }
            _ => None,
        }
    }

    fn ground_seq_len(ast: &Dynamic) -> Option<usize> {
        match ast.decl().kind() {
            DeclKind::SEQ_UNIT => Some(1),
            DeclKind::SEQ_EMPTY => Some(0),
            DeclKind::SEQ_CONCAT => ast
                .children()
                .into_iter()
                .map(|child| Self::ground_seq_len(&child))
                .sum(),
            _ => None,
        }
    }

    fn builtin_nat_decls(&self, solver: &Z3Solver) -> Result<Rc<BuiltinNatDecls>, String> {
        if let Some(decls) = self.builtin_nat_decls.borrow().as_ref().cloned() {
            return Ok(decls);
        }

        let nat_ty = Self::nat_spec_ty();
        let nat_composite = self.composite_encoding(&nat_ty, solver)?;
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

        let nat_to_int = RecFuncDecl::new("builtin_nat_to_int", &[&self.value_sort], &Sort::int());
        let int_to_nat = RecFuncDecl::new("builtin_int_to_nat", &[&Sort::int()], &self.value_sort);

        let int_arg = Int::new_const("builtin_int_to_nat_arg");
        let zero_value = zero_ctor.symbol.apply(&[]);
        let int_minus_one = int_arg.clone() - Int::from_i64(1);
        let succ_tail = int_to_nat.apply(&[&int_minus_one]);
        let succ_value = succ_ctor.symbol.apply(&[&succ_tail]);
        let int_to_nat_body = int_arg.le(0).ite(&zero_value, &succ_value);
        int_to_nat.add_def(&[&int_arg], &int_to_nat_body);

        let nat_arg = Dynamic::new_const("builtin_nat_to_int_arg", &self.value_sort);
        let nat_value = SymValue::new(nat_arg.clone());
        let zero_case = self.tag_formula(&nat_composite, zero_index, &nat_value)?;
        let succ_field =
            self.project_composite_ctor_field(&nat_composite, succ_index, &nat_value, 0)?;
        let succ_int = nat_to_int
            .apply(&[succ_field.ast()])
            .as_int()
            .ok_or_else(|| "builtin_nat_to_int must return Int".to_owned())?;
        let nat_to_int_body = zero_case.ite(&Int::from_i64(0), &(Int::from_i64(1) + succ_int));
        nat_to_int.add_def(&[&nat_arg], &nat_to_int_body);

        let decls = Rc::new(BuiltinNatDecls {
            nat_to_int,
            int_to_nat,
        });
        self.builtin_nat_decls.replace(Some(decls.clone()));
        Ok(decls)
    }

    fn nat_spec_ty() -> SpecTy {
        SpecTy::Enum {
            name: "Nat".to_owned(),
            args: vec![],
        }
    }

    fn nat_ctor_indices(&self, solver: &Z3Solver) -> Result<(usize, usize), String> {
        let composite = self.composite_encoding(&Self::nat_spec_ty(), solver)?;
        let zero = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| ctor.fields.is_empty())
            .map(|(index, _)| index)
            .ok_or_else(|| "Nat is missing `Zero`".to_owned())?;
        let succ = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| ctor.fields.len() == 1)
            .map(|(index, _)| index)
            .ok_or_else(|| "Nat is missing `Succ`".to_owned())?;
        Ok((zero, succ))
    }

    fn try_concrete_nat_usize(
        &self,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Option<u64>, String> {
        let nat_ty = Self::nat_spec_ty();
        let composite = self.composite_encoding(&nat_ty, solver)?;
        let (zero, succ) = self.nat_ctor_indices(solver)?;
        match Self::ground_ctor_index_for_composite(&composite, value) {
            Some(index) if index == zero => Ok(Some(0)),
            Some(index) if index == succ => {
                let tail = self.project_composite_ctor_field(&composite, succ, value, 0)?;
                Ok(self.try_concrete_nat_usize(&tail, solver)?.map(|n| n + 1))
            }
            _ => Ok(None),
        }
    }

    fn ground_ctor_index_for_composite(
        composite: &CompositeEncoding,
        value: &SymValue,
    ) -> Option<usize> {
        let decl_name = value.dynamic().decl().name();
        composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| decl_name == ctor.symbol.name())
            .map(|(index, _)| index)
    }

    pub(crate) fn bool_value(&self, value: bool) -> SymValue {
        self.wrap_bool(&Bool::from_bool(value))
    }

    fn rust_ty_value_with_z3(&self, key: &RustTyKey, solver: &Z3Solver) -> SymValue {
        let value = {
            let mut values = self.rust_ty_values.borrow_mut();
            values
                .entry(key.clone())
                .or_insert_with(|| {
                    SymValue::new(Dynamic::new_const(
                        format!("rust_ty_{}", self.sanitize_name(key.as_str())),
                        &self.value_sort,
                    ))
                })
                .clone()
        };

        let values = self.rust_ty_values.borrow();
        let mut asserted = self.asserted_rust_ty_distinct.borrow_mut();
        for (other_key, other_value) in values.iter() {
            if other_key == key {
                continue;
            }
            let pair = if key < other_key {
                (key.clone(), other_key.clone())
            } else {
                (other_key.clone(), key.clone())
            };
            if asserted.insert(pair) {
                solver.assert(value.dynamic().eq(other_value.dynamic()).not());
            }
        }
        value
    }

    pub(crate) fn int_value(&self, value: i64) -> SymValue {
        self.wrap_int(&Int::from_i64(value))
    }

    pub(crate) fn decimal_int_value(&self, digits: &str) -> Result<SymValue, String> {
        let int =
            Int::from_str(digits).map_err(|()| format!("invalid integer literal {digits}"))?;
        Ok(self.wrap_int(&int))
    }

    pub(crate) fn bool_term(&self, value: &SymValue) -> Bool {
        if let Some(payload) = self.boxed_payload(value, &self.bool_encoding.boxed) {
            return payload.as_bool().expect("boxed bool payload");
        }
        self.bool_encoding
            .unboxed
            .apply(&[value.ast()])
            .as_bool()
            .expect("boxed bool payload")
    }

    pub(crate) fn int_term(&self, value: &SymValue) -> Int {
        if let Some(payload) = self.boxed_payload(value, &self.int_encoding.boxed) {
            return payload.as_int().expect("boxed int payload");
        }
        self.int_encoding
            .unboxed
            .apply(&[value.ast()])
            .as_int()
            .expect("boxed int payload")
    }

    fn boxed_payload(&self, value: &SymValue, boxed: &FuncDecl) -> Option<Dynamic> {
        let ast = value.dynamic();
        if ast.decl().name() != boxed.name() {
            return None;
        }
        let children = ast.children();
        match children.as_slice() {
            [payload] => Some(payload.clone()),
            _ => None,
        }
    }

    fn eq_for_spec_ty_with_z3(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Bool, String> {
        if let Some(equal) = self.try_ground_eq_for_spec_ty(ty, lhs, rhs)? {
            return Ok(Bool::from_bool(equal));
        }
        if let Some(equal) = self.try_direct_composite_eq_for_spec_ty(ty, lhs, rhs, solver)? {
            return Ok(equal);
        }
        let encoding = self.type_encoding(ty, solver)?;
        Ok(match &encoding.kind {
            TypeEncodingKind::Bool => self.bool_term(lhs).eq(self.bool_term(rhs)),
            TypeEncodingKind::Int => self.int_term(lhs).eq(self.int_term(rhs)),
            TypeEncodingKind::Opaque => lhs.dynamic().eq(rhs.dynamic()),
            TypeEncodingKind::Seq => lhs.dynamic().eq(rhs.dynamic()),
            TypeEncodingKind::Composite(_) => lhs.dynamic().eq(rhs.dynamic()),
        })
    }

    fn try_ground_eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<Option<bool>, String> {
        match ty {
            SpecTy::Seq(item_ty) => {
                let Some(lhs_len) = Self::ground_seq_len(lhs.dynamic()) else {
                    return Ok(None);
                };
                let Some(rhs_len) = Self::ground_seq_len(rhs.dynamic()) else {
                    return Ok(None);
                };
                if lhs_len != rhs_len {
                    return Ok(Some(false));
                }
                for index in 0..lhs_len {
                    let lhs_item = SymValue::new(
                        Self::ground_seq_nth(lhs.dynamic(), index)
                            .expect("ground sequence length implies in-range nth"),
                    );
                    let rhs_item = SymValue::new(
                        Self::ground_seq_nth(rhs.dynamic(), index)
                            .expect("ground sequence length implies in-range nth"),
                    );
                    let Some(equal) =
                        self.try_ground_eq_for_spec_ty(item_ty, &lhs_item, &rhs_item)?
                    else {
                        return Ok(None);
                    };
                    if !equal {
                        return Ok(Some(false));
                    }
                }
                Ok(Some(true))
            }
            SpecTy::Bool => Ok(self
                .bool_term(lhs)
                .as_bool()
                .zip(self.bool_term(rhs).as_bool())
                .map(|(lhs, rhs)| lhs == rhs)),
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
            | SpecTy::Usize => Ok(self
                .int_term(lhs)
                .as_i64()
                .zip(self.int_term(rhs).as_i64())
                .map(|(lhs, rhs)| lhs == rhs)),
            SpecTy::Tuple(_)
            | SpecTy::Struct { .. }
            | SpecTy::Enum { .. }
            | SpecTy::Ref(_)
            | SpecTy::Mut(_) => self.try_ground_composite_eq_for_spec_ty(ty, lhs, rhs),
            SpecTy::TypeParam(_) => Ok(None),
        }
    }

    fn try_ground_composite_eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> Result<Option<bool>, String> {
        let encoding = self.unasserted_type_encoding(ty)?;
        let TypeEncodingKind::Composite(composite) = &encoding.kind else {
            return Ok(None);
        };
        let lhs_ctor = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| lhs.dynamic().decl().name() == ctor.symbol.name());
        let rhs_ctor = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| rhs.dynamic().decl().name() == ctor.symbol.name());
        let (Some((lhs_index, lhs_ctor)), Some((rhs_index, rhs_ctor))) = (lhs_ctor, rhs_ctor)
        else {
            return Ok(None);
        };
        if lhs_index != rhs_index {
            return Ok(Some(false));
        }
        let lhs_children = lhs.dynamic().children();
        let rhs_children = rhs.dynamic().children();
        if lhs_children.len() != lhs_ctor.fields.len()
            || rhs_children.len() != rhs_ctor.fields.len()
        {
            return Ok(None);
        }
        for (field, lhs_child, rhs_child) in lhs_ctor
            .fields
            .iter()
            .zip(lhs_children)
            .zip(rhs_children)
            .map(|((field, lhs_child), rhs_child)| (field, lhs_child, rhs_child))
        {
            let lhs_child = SymValue::new(lhs_child);
            let rhs_child = SymValue::new(rhs_child);
            let Some(equal) = self.try_ground_eq_for_spec_ty(&field.ty, &lhs_child, &rhs_child)?
            else {
                return Ok(None);
            };
            if !equal {
                return Ok(Some(false));
            }
        }
        Ok(Some(true))
    }

    fn try_direct_composite_eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Option<Bool>, String> {
        let encoding = self.unasserted_type_encoding(ty)?;
        let TypeEncodingKind::Composite(composite) = &encoding.kind else {
            return Ok(None);
        };
        let lhs_ctor = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| lhs.dynamic().decl().name() == ctor.symbol.name());
        let rhs_ctor = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| rhs.dynamic().decl().name() == ctor.symbol.name());
        let (Some((lhs_index, lhs_ctor)), Some((rhs_index, rhs_ctor))) = (lhs_ctor, rhs_ctor)
        else {
            return Ok(None);
        };
        if lhs_index != rhs_index {
            return Ok(Some(Bool::from_bool(false)));
        }

        let lhs_children = lhs.dynamic().children();
        let rhs_children = rhs.dynamic().children();
        if lhs_children.len() != lhs_ctor.fields.len()
            || rhs_children.len() != rhs_ctor.fields.len()
        {
            return Ok(None);
        }

        let mut fields = Vec::with_capacity(lhs_ctor.fields.len());
        for (field, lhs_child, rhs_child) in lhs_ctor
            .fields
            .iter()
            .zip(lhs_children)
            .zip(rhs_children)
            .map(|((field, lhs_child), rhs_child)| (field, lhs_child, rhs_child))
        {
            fields.push(self.eq_for_spec_ty_with_z3(
                &field.ty,
                &SymValue::new(lhs_child),
                &SymValue::new(rhs_child),
                solver,
            )?);
        }
        Ok(Some(bool_conjoin(fields)))
    }

    pub(crate) fn lower_unary_value(&self, op: UnaryOp, value: &SymValue) -> SymValue {
        match op {
            UnaryOp::Not => self.wrap_bool(&self.bool_term(value).not()),
            UnaryOp::Neg => self.wrap_int(&(Int::from_i64(0) - self.int_term(value))),
        }
    }

    pub(crate) fn lower_bool_not_value(&self, value: &SymValue) -> SymValue {
        self.wrap_bool(&self.bool_term(value).not())
    }

    pub(crate) fn lower_int_neg_value(&self, value: &SymValue) -> IntValueResult {
        let term = Int::from_i64(0) - self.int_term(value);
        let value = self.wrap_int(&term);
        IntValueResult { term, value }
    }

    pub(crate) fn lower_int_binary_value(
        &self,
        op: IntValueBinaryOp,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> IntValueResult {
        let term = match op {
            IntValueBinaryOp::Add => self.int_term(lhs) + self.int_term(rhs),
            IntValueBinaryOp::Sub => self.int_term(lhs) - self.int_term(rhs),
            IntValueBinaryOp::Mul => self.int_term(lhs) * self.int_term(rhs),
        };
        let value = self.wrap_int(&term);
        IntValueResult { term, value }
    }

    fn lower_eq_value_with_z3(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        negated: bool,
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        let eq = self.eq_for_spec_ty_with_z3(ty, lhs, rhs, solver)?;
        let formula = if negated { eq.not() } else { eq };
        Ok(self.wrap_bool(&formula))
    }

    pub(crate) fn lower_int_predicate_value(
        &self,
        op: IntValuePredicateOp,
        lhs: &SymValue,
        rhs: &SymValue,
    ) -> SymValue {
        let lhs = self.int_term(lhs);
        let rhs = self.int_term(rhs);
        let formula = match op {
            IntValuePredicateOp::Lt => lhs.lt(rhs),
            IntValuePredicateOp::Le => lhs.le(rhs),
            IntValuePredicateOp::Gt => lhs.gt(rhs),
            IntValuePredicateOp::Ge => lhs.ge(rhs),
        };
        self.wrap_bool(&formula)
    }

    fn lower_binary_value_with_z3(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        Ok(match op {
            BinaryOp::Eq => self.wrap_bool(&self.eq_for_spec_ty_with_z3(lhs_ty, lhs, rhs, solver)?),
            BinaryOp::Ne => {
                self.wrap_bool(&self.eq_for_spec_ty_with_z3(lhs_ty, lhs, rhs, solver)?.not())
            }
            BinaryOp::And => {
                self.wrap_bool(&Bool::and(&[&self.bool_term(lhs), &self.bool_term(rhs)]))
            }
            BinaryOp::Or => {
                self.wrap_bool(&Bool::or(&[&self.bool_term(lhs), &self.bool_term(rhs)]))
            }
            BinaryOp::Lt => self.wrap_bool(&self.int_term(lhs).lt(self.int_term(rhs))),
            BinaryOp::Le => self.wrap_bool(&self.int_term(lhs).le(self.int_term(rhs))),
            BinaryOp::Gt => self.wrap_bool(&self.int_term(lhs).gt(self.int_term(rhs))),
            BinaryOp::Ge => self.wrap_bool(&self.int_term(lhs).ge(self.int_term(rhs))),
            BinaryOp::Add => self.wrap_int(&(self.int_term(lhs) + self.int_term(rhs))),
            BinaryOp::Sub => self.wrap_int(&(self.int_term(lhs) - self.int_term(rhs))),
            BinaryOp::Mul => self.wrap_int(&(self.int_term(lhs) * self.int_term(rhs))),
            BinaryOp::BitAnd => {
                let lhs = BV::from_int(&self.int_term(lhs), self.pointer_width_bits as u32);
                let rhs = BV::from_int(&self.int_term(rhs), self.pointer_width_bits as u32);
                self.wrap_int(&(lhs & rhs).to_int(false))
            }
            BinaryOp::Rem if matches!(lhs_ty, SpecTy::Enum { name, args } if name == "Nat" && args.is_empty()) => {
                self.wrap_int(&(self.nat_to_int_term_with_z3(lhs, solver)? % self.int_term(rhs)))
            }
            BinaryOp::Rem => self.wrap_int(&(self.int_term(lhs) % self.int_term(rhs))),
            BinaryOp::Concat => {
                let lhs = self.seq_term(lhs)?;
                let rhs = self.seq_term(rhs)?;
                SymValue::new(Dynamic::from(Z3Seq::concat(&[&lhs, &rhs])))
            }
        })
    }

    fn lower_binary_predicate_with_z3(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Option<Bool>, String> {
        Ok(Some(match op {
            BinaryOp::Eq => self.eq_for_spec_ty_with_z3(lhs_ty, lhs, rhs, solver)?,
            BinaryOp::Ne => self.eq_for_spec_ty_with_z3(lhs_ty, lhs, rhs, solver)?.not(),
            BinaryOp::Lt => self.int_term(lhs).lt(self.int_term(rhs)),
            BinaryOp::Le => self.int_term(lhs).le(self.int_term(rhs)),
            BinaryOp::Gt => self.int_term(lhs).gt(self.int_term(rhs)),
            BinaryOp::Ge => self.int_term(lhs).ge(self.int_term(rhs)),
            BinaryOp::And
            | BinaryOp::Or
            | BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Mul
            | BinaryOp::BitAnd
            | BinaryOp::Rem
            | BinaryOp::Concat => {
                return Ok(None);
            }
        }))
    }

    fn construct_composite_with_z3(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        self.construct_composite_ctor_with_z3(ty, 0, fields, solver)
    }

    fn construct_composite_ctor_with_z3(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        let composite = self.composite_encoding(ty, solver)?;
        let ctor = composite
            .constructors
            .get(ctor_index)
            .ok_or_else(|| format!("constructor index {ctor_index} out of range"))?;
        if fields.len() != ctor.fields.len() {
            return Err(format!(
                "constructor `{}` expects {} fields, found {}",
                ctor.name,
                ctor.fields.len(),
                fields.len()
            ));
        }
        let args = fields.iter().map(SymValue::ast).collect::<Vec<_>>();
        Ok(SymValue::new(ctor.symbol.apply(&args)))
    }

    fn construct_composite_ctor_without_axioms(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
    ) -> Result<SymValue, String> {
        let encoding = self.unasserted_type_encoding(ty)?;
        let TypeEncodingKind::Composite(composite) = &encoding.kind else {
            return Err(format!("expected composite-backed spec type, found {ty:?}"));
        };
        let ctor = composite
            .constructors
            .get(ctor_index)
            .ok_or_else(|| format!("constructor index {ctor_index} out of range"))?;
        if fields.len() != ctor.fields.len() {
            return Err(format!(
                "constructor `{}` expects {} fields, found {}",
                ctor.name,
                ctor.fields.len(),
                fields.len()
            ));
        }
        let args = fields.iter().map(SymValue::ast).collect::<Vec<_>>();
        Ok(SymValue::new(ctor.symbol.apply(&args)))
    }

    pub(crate) fn construct_option_none(&self, inner: SpecTy) -> Result<SymValue, String> {
        let ctor_index = self.enum_ctor_index("Option", "None")?;
        self.construct_composite_ctor_without_axioms(&option_spec_ty(inner), ctor_index, &[])
    }

    pub(crate) fn construct_option_some(
        &self,
        inner: SpecTy,
        value: SymValue,
    ) -> Result<SymValue, String> {
        let ctor_index = self.enum_ctor_index("Option", "Some")?;
        self.construct_composite_ctor_without_axioms(&option_spec_ty(inner), ctor_index, &[value])
    }

    fn checked_result_tuple_value_with_z3(
        &self,
        result_ty: SpecTy,
        result_value: SymValue,
        overflow_value: SymValue,
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        self.construct_composite_with_z3(
            &SpecTy::Tuple(vec![result_ty, SpecTy::Bool]),
            &[result_value, overflow_value],
            solver,
        )
    }

    fn fresh_for_spec_ty_with_z3(
        &self,
        ty: &SpecTy,
        hint: &str,
        solver: &Z3Solver,
        fresh_name: &mut impl FnMut(&str) -> String,
    ) -> Result<SymValue, String> {
        if matches!(ty, SpecTy::Enum { .. }) {
            return Ok(SymValue::new(Dynamic::new_const(
                fresh_name(hint),
                &self.value_sort,
            )));
        }
        let encoding = self.type_encoding(ty, solver)?;
        self.fresh_for_encoding(&encoding, hint, solver, fresh_name)
    }

    fn project_field_with_z3(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        index: usize,
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        let composite = self.composite_encoding(ty, solver)?;
        self.project_composite_field(&composite, value, index)
    }

    fn project_composite_field(
        &self,
        composite: &CompositeEncoding,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        self.project_composite_ctor_field(composite, 0, value, index)
    }

    fn project_composite_ctor_field(
        &self,
        composite: &CompositeEncoding,
        ctor_index: usize,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        let ctor = composite
            .constructors
            .get(ctor_index)
            .ok_or_else(|| format!("constructor index {ctor_index} out of range"))?;
        let field = ctor
            .fields
            .get(index)
            .ok_or_else(|| format!("field index {index} out of range"))?;
        if value.dynamic().decl().name() == ctor.symbol.name() {
            let children = value.dynamic().children();
            if let Some(payload) = children.get(index) {
                return Ok(SymValue::new(payload.clone()));
            }
        }
        Ok(SymValue::new(field.inverse.apply(&[value.ast()])))
    }

    fn project_composite_ctor_field_for_ty_with_z3(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
        index: usize,
        solver: &Z3Solver,
    ) -> Result<SymValue, String> {
        let composite = self.composite_encoding(ty, solver)?;
        self.project_composite_ctor_field(&composite, ctor_index, value, index)
    }

    fn composite_ctor_view_for_ty_with_z3(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<CompositeCtorView, String> {
        let composite = self.composite_encoding(ty, solver)?;
        let ctor = composite
            .constructors
            .get(ctor_index)
            .ok_or_else(|| format!("constructor index {ctor_index} out of range"))?;
        let tag = self.tag_formula(&composite, ctor_index, value)?;
        let fields = ctor
            .fields
            .iter()
            .enumerate()
            .map(|(field_index, field)| {
                Ok((
                    field.ty.clone(),
                    self.project_composite_ctor_field(&composite, ctor_index, value, field_index)?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(CompositeCtorView { tag, fields })
    }

    fn direct_composite_ctor_fields(
        &self,
        composite: &CompositeEncoding,
        value: &SymValue,
    ) -> Result<Option<DirectCtorFields>, String> {
        let Some((ctor_index, ctor)) = composite
            .constructors
            .iter()
            .enumerate()
            .find(|(_, ctor)| value.dynamic().decl().name() == ctor.symbol.name())
        else {
            return Ok(None);
        };
        let fields = ctor
            .fields
            .iter()
            .enumerate()
            .map(|(field_index, field)| {
                Ok((
                    field.ty.clone(),
                    self.project_composite_ctor_field(composite, ctor_index, value, field_index)?,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Some(DirectCtorFields { ctor_index, fields }))
    }

    fn direct_composite_ctor_fields_for_ty_with_z3(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Option<DirectCtorFields>, String> {
        let composite = self.composite_encoding(ty, solver)?;
        self.direct_composite_ctor_fields(&composite, value)
    }

    fn tag_formula(
        &self,
        composite: &CompositeEncoding,
        ctor_index: usize,
        value: &SymValue,
    ) -> Result<Bool, String> {
        let ctor = composite
            .constructors
            .get(ctor_index)
            .ok_or_else(|| format!("constructor index {ctor_index} out of range"))?;
        let decl_name = value.dynamic().decl().name();
        if decl_name == ctor.symbol.name() {
            return Ok(Bool::from_bool(true));
        }
        if composite
            .constructors
            .iter()
            .any(|other| decl_name == other.symbol.name())
        {
            return Ok(Bool::from_bool(false));
        }
        Ok(composite
            .tag_function
            .apply(&[value.ast()])
            .as_int()
            .expect("tag result")
            .eq(&ctor.tag))
    }

    fn tag_formula_for_ty_with_z3(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Bool, String> {
        let composite = self.composite_encoding(ty, solver)?;
        self.tag_formula(&composite, ctor_index, value)
    }

    fn ground_ctor_index_with_z3(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Option<usize>, String> {
        let composite = self.composite_encoding(ty, solver)?;
        Ok(Self::ground_ctor_index_for_composite(&composite, value))
    }

    fn fresh_for_encoding(
        &self,
        encoding: &TypeEncoding,
        hint: &str,
        solver: &Z3Solver,
        fresh_name: &mut impl FnMut(&str) -> String,
    ) -> Result<SymValue, String> {
        match &encoding.kind {
            TypeEncodingKind::Bool => Ok(self.wrap_bool(&Bool::new_const(fresh_name(hint)))),
            TypeEncodingKind::Int => Ok(self.wrap_int(&Int::new_const(fresh_name(hint)))),
            TypeEncodingKind::Opaque => Ok(SymValue::new(Dynamic::new_const(
                fresh_name(hint),
                &self.value_sort,
            ))),
            TypeEncodingKind::Seq => Ok(SymValue::new(Dynamic::from(Z3Seq::new_const(
                fresh_name(hint),
                &self.value_sort,
            )))),
            TypeEncodingKind::Composite(composite) => {
                let ctor = composite.single_constructor()?;
                let mut fields = Vec::with_capacity(ctor.fields.len());
                for (index, field) in ctor.fields.iter().enumerate() {
                    fields.push(self.fresh_for_spec_ty_with_z3(
                        &field.ty,
                        &format!("{hint}_{index}"),
                        solver,
                        fresh_name,
                    )?);
                }
                let args = fields.iter().map(SymValue::ast).collect::<Vec<_>>();
                Ok(SymValue::new(ctor.symbol.apply(&args)))
            }
        }
    }

    pub(crate) fn int_bounds(&self, ty: &SpecTy) -> Result<Option<(Int, Int)>, String> {
        Ok(Some(match ty {
            SpecTy::Int => return Ok(None),
            SpecTy::IntLiteral => return Ok(None),
            SpecTy::I8 => (Int::from_i64(i8::MIN.into()), Int::from_i64(i8::MAX.into())),
            SpecTy::I16 => (
                Int::from_i64(i16::MIN.into()),
                Int::from_i64(i16::MAX.into()),
            ),
            SpecTy::I32 => (
                Int::from_i64(i32::MIN.into()),
                Int::from_i64(i32::MAX.into()),
            ),
            SpecTy::I64 => (Int::from_i64(i64::MIN), Int::from_i64(i64::MAX)),
            SpecTy::Isize => self.pointer_sized_int_bounds(true)?,
            SpecTy::U8 => (Int::from_u64(0), Int::from_u64(u8::MAX.into())),
            SpecTy::U16 => (Int::from_u64(0), Int::from_u64(u16::MAX.into())),
            SpecTy::U32 => (Int::from_u64(0), Int::from_u64(u32::MAX.into())),
            SpecTy::U64 => (Int::from_u64(0), Int::from_u64(u64::MAX)),
            SpecTy::Usize => self.pointer_sized_int_bounds(false)?,
            other => {
                return Err(format!(
                    "expected integer-backed spec type, found {other:?}"
                ));
            }
        }))
    }

    fn build_type_encoding(&self, ty: &SpecTy) -> Result<Rc<TypeEncoding>, String> {
        let (kind, sort) = match ty {
            SpecTy::Bool => (TypeEncodingKind::Bool, self.value_sort.clone()),
            SpecTy::RustTy => (TypeEncodingKind::Opaque, self.value_sort.clone()),
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
            | SpecTy::Usize => (TypeEncodingKind::Int, self.value_sort.clone()),
            SpecTy::Seq(_) => (TypeEncodingKind::Seq, self.seq_value_sort.clone()),
            SpecTy::Tuple(_)
            | SpecTy::Struct { .. }
            | SpecTy::Enum { .. }
            | SpecTy::Ref(_)
            | SpecTy::Mut(_) => (
                TypeEncodingKind::Composite(self.build_composite_encoding(ty)?),
                self.value_sort.clone(),
            ),
            SpecTy::TypeParam(_) => (TypeEncodingKind::Opaque, self.value_sort.clone()),
        };
        Ok(Rc::new(TypeEncoding { kind, sort }))
    }

    fn unasserted_type_encoding(&self, ty: &SpecTy) -> Result<Rc<TypeEncoding>, String> {
        let cached = { self.type_encodings.borrow().get(ty).cloned() };
        if let Some(encoding) = cached {
            return Ok(encoding);
        }
        let encoding = self.build_type_encoding(ty)?;
        self.type_encodings
            .borrow_mut()
            .insert(ty.clone(), encoding.clone());
        Ok(encoding)
    }

    fn build_composite_encoding(&self, ty: &SpecTy) -> Result<Rc<CompositeEncoding>, String> {
        if let SpecTy::Enum { name, args } = ty {
            return self.build_named_composite_encoding(name, args);
        }

        let ctor_specs = self.composite_ctor_specs(ty)?;
        let sort_name = self.type_name(ty);
        let subtype_id = self.next_subtype_id.get();
        self.next_subtype_id.set(subtype_id + 1);

        let tag_function = FuncDecl::new(
            format!("ctortag{subtype_id}"),
            &[&self.value_sort],
            &Sort::int(),
        );
        let constructors = ctor_specs
            .into_iter()
            .map(
                |(ctor_name, fields)| -> Result<Rc<ConstructorEncoding>, String> {
                    let constructor_name = if ctor_name.is_empty() {
                        format!("mk_{sort_name}")
                    } else {
                        format!("mk_{sort_name}_{ctor_name}")
                    };
                    let constructor_tag = Int::from_u64(u64::from(self.next_ctor_tag.get()));
                    self.next_ctor_tag.set(self.next_ctor_tag.get() + 1);
                    let field_sorts = fields
                        .iter()
                        .map(|(_, field_ty)| self.sort_for_spec_ty(field_ty))
                        .collect::<Result<Vec<_>, _>>()?;
                    let domain_sorts = field_sorts.iter().collect::<Vec<_>>();
                    let constructor_symbol =
                        FuncDecl::new(constructor_name.as_str(), &domain_sorts, &self.value_sort);
                    let fields = fields
                        .into_iter()
                        .map(|(label, field_ty)| {
                            Ok(FieldEncoding {
                                inverse: FuncDecl::new(
                                    if ctor_name.is_empty() {
                                        format!("ctorinv_{sort_name}_{label}")
                                    } else {
                                        format!("ctorinv_{sort_name}_{ctor_name}_{label}")
                                    },
                                    &[&self.value_sort],
                                    &self.sort_for_spec_ty(&field_ty)?,
                                ),
                                ty: field_ty,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    Ok(Rc::new(ConstructorEncoding {
                        name: constructor_name,
                        symbol: constructor_symbol,
                        fields,
                        tag: constructor_tag,
                    }))
                },
            )
            .collect::<Result<Vec<_>, String>>()?;
        let composite = Rc::new(CompositeEncoding {
            tag_function,
            constructors,
            invariant: matches!(ty, SpecTy::Enum { .. }).then(|| {
                Rc::new(FuncDecl::new(
                    format!("inv_{sort_name}"),
                    &[&self.value_sort],
                    &Sort::bool(),
                ))
            }),
        });
        Ok(composite)
    }

    fn build_named_composite_encoding(
        &self,
        name: &str,
        type_args: &[SpecTy],
    ) -> Result<Rc<CompositeEncoding>, String> {
        let family = self.enum_family_encoding(name)?;
        let ctor_specs = self.named_ctor_specs(name, type_args)?;
        if family.constructors.len() != ctor_specs.len() {
            return Err(format!(
                "enum family `{name}` constructor shape mismatch: expected {}, found {}",
                family.constructors.len(),
                ctor_specs.len()
            ));
        }

        let constructors = family
            .constructors
            .iter()
            .zip(ctor_specs)
            .map(
                |(family_ctor, (_ctor_name, fields))| -> Result<Rc<ConstructorEncoding>, String> {
                    let field_sorts = fields
                        .iter()
                        .map(|(_, ty)| self.sort_for_spec_ty(ty))
                        .collect::<Result<Vec<_>, _>>()?;
                    let domain_sorts = field_sorts.iter().collect::<Vec<_>>();
                    Ok(Rc::new(ConstructorEncoding {
                        name: family_ctor.symbol_name.clone(),
                        symbol: FuncDecl::new(
                            family_ctor.symbol_name.as_str(),
                            &domain_sorts,
                            &self.value_sort,
                        ),
                        fields: fields
                            .into_iter()
                            .enumerate()
                            .map(|(index, (_label, ty))| {
                                Ok(FieldEncoding {
                                    inverse: FuncDecl::new(
                                        family_ctor.inverse_names[index].as_str(),
                                        &[&self.value_sort],
                                        &self.sort_for_spec_ty(&ty)?,
                                    ),
                                    ty,
                                })
                            })
                            .collect::<Result<Vec<_>, String>>()?,
                        tag: Int::from_u64(u64::from(family_ctor.tag_value)),
                    }))
                },
            )
            .collect::<Result<Vec<_>, String>>()?;

        let invariant_name = format!("inv_{}", self.instantiated_named_type_name(name, type_args));
        Ok(Rc::new(CompositeEncoding {
            tag_function: FuncDecl::new(
                family.tag_function_name.as_str(),
                &[&self.value_sort],
                &Sort::int(),
            ),
            constructors,
            invariant: Some(Rc::new(FuncDecl::new(
                invariant_name,
                &[&self.value_sort],
                &Sort::bool(),
            ))),
        }))
    }

    fn enum_family_encoding(&self, name: &str) -> Result<Rc<EnumFamilyEncoding>, String> {
        if let Some(encoding) = self.enum_family_encodings.borrow().get(name).cloned() {
            return Ok(encoding);
        }

        let enum_def = self
            .enum_defs
            .borrow()
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown spec enum `{name}`"))?;
        let family_sort_name = self.enum_family_name(&enum_def.name);
        let subtype_id = self.next_subtype_id.get();
        self.next_subtype_id.set(subtype_id + 1);
        let tag_function_name = format!("ctortag{subtype_id}");
        let constructors = enum_def
            .ctors
            .iter()
            .map(|ctor| {
                let symbol_name = format!("mk_{family_sort_name}_{}", ctor.name);
                let tag_value = self.next_ctor_tag.get();
                self.next_ctor_tag.set(tag_value + 1);
                let inverse_names = ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(index, _)| format!("ctorinv_{family_sort_name}_{}_{}", ctor.name, index))
                    .collect();
                Rc::new(EnumFamilyCtorEncoding {
                    symbol_name,
                    inverse_names,
                    tag_value,
                })
            })
            .collect::<Vec<_>>();

        let encoding = Rc::new(EnumFamilyEncoding {
            tag_function_name,
            constructors,
        });
        self.enum_family_encodings
            .borrow_mut()
            .insert(name.to_owned(), encoding.clone());
        Ok(encoding)
    }

    fn assert_type_axioms(
        &self,
        ty: &SpecTy,
        encoding: &TypeEncoding,
        solver: &Z3Solver,
    ) -> Result<(), String> {
        match &encoding.kind {
            TypeEncodingKind::Bool
            | TypeEncodingKind::Int
            | TypeEncodingKind::Opaque
            | TypeEncodingKind::Seq => Ok(()),
            TypeEncodingKind::Composite(composite) => {
                if matches!(ty, SpecTy::Enum { .. }) {
                    self.assert_composite_axioms(composite, solver)?;
                    self.assert_named_invariant_axioms(ty, composite, solver)?;
                }
                Ok(())
            }
        }
    }

    fn ensure_primitive_axioms(&self, solver: &Z3Solver) {
        let _ = solver;
        if self.primitive_axioms_asserted.get() {
            return;
        }
        self.primitive_axioms_asserted.set(true);
    }

    fn assert_composite_axioms(
        &self,
        composite: &CompositeEncoding,
        solver: &Z3Solver,
    ) -> Result<(), String> {
        for ctor in &composite.constructors {
            let args = ctor
                .fields
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    Ok(Dynamic::new_const(
                        format!("{}_arg_{index}", ctor.name),
                        &self.sort_for_spec_ty(&field.ty)?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let arg_refs = args.iter().map(|arg| arg as &dyn Ast).collect::<Vec<_>>();
            let constructor_app = ctor.symbol.apply(&arg_refs);
            let tag_eq = composite
                .tag_function
                .apply(&[&constructor_app])
                .as_int()
                .expect("composite tag")
                .eq(&ctor.tag);
            self.assert_patterned_forall(solver, &arg_refs, &constructor_app, &tag_eq);

            for (index, field) in ctor.fields.iter().enumerate() {
                let body = field.inverse.apply(&[&constructor_app]).eq(&args[index]);
                self.assert_patterned_forall(solver, &arg_refs, &constructor_app, &body);
            }
        }

        if let Ok(ctor) = composite.single_constructor()
            && !ctor.fields.is_empty()
        {
            let value = Dynamic::new_const(format!("{}_eta_value", ctor.name), &self.value_sort);
            let projected_args = ctor
                .fields
                .iter()
                .map(|field| field.inverse.apply(&[&value]))
                .collect::<Vec<_>>();
            let arg_refs = projected_args
                .iter()
                .map(|arg| arg as &dyn Ast)
                .collect::<Vec<_>>();
            let reconstructed = ctor.symbol.apply(&arg_refs);
            let body = reconstructed.eq(&value);
            let pattern = Pattern::new(&[&reconstructed]);
            solver.assert(ast::forall_const(&[&value], &[&pattern], &body));
        }
        Ok(())
    }

    fn assert_named_invariant_axioms(
        &self,
        ty: &SpecTy,
        composite: &CompositeEncoding,
        solver: &Z3Solver,
    ) -> Result<(), String> {
        let Some(invariant) = &composite.invariant else {
            return Ok(());
        };

        for ctor in &composite.constructors {
            let args = ctor
                .fields
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    Ok(Dynamic::new_const(
                        format!("{}_inv_arg_{index}", ctor.name),
                        &self.sort_for_spec_ty(&field.ty)?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let arg_refs = args.iter().map(|arg| arg as &dyn Ast).collect::<Vec<_>>();
            let constructor_app = ctor.symbol.apply(&arg_refs);
            let inv_app = invariant
                .apply(&[&constructor_app])
                .as_bool()
                .expect("named invariant predicate");
            let mut antecedent = Vec::new();
            for (index, field) in ctor.fields.iter().enumerate() {
                let value = SymValue::new(args[index].clone());
                if let Some(formula) = self.field_invariant_formula(&field.ty, &value, solver)? {
                    antecedent.push(formula);
                }
            }
            let body = bool_implies(bool_conjoin(antecedent), inv_app);
            self.assert_patterned_forall(solver, &arg_refs, &constructor_app, &body);
        }

        let value = Dynamic::new_const(
            format!("{}_inv_value", self.type_name(ty)),
            &self.value_sort,
        );
        let inv_app = invariant
            .apply(&[&value])
            .as_bool()
            .expect("named invariant predicate");
        let value_sym = SymValue::new(value.clone());
        let mut branches = Vec::new();
        for (ctor_index, ctor) in composite.constructors.iter().enumerate() {
            let mut formulas = vec![self.tag_formula(composite, ctor_index, &value_sym)?];
            for (field_index, field) in ctor.fields.iter().enumerate() {
                let field_value = self.project_composite_ctor_field(
                    composite,
                    ctor_index,
                    &value_sym,
                    field_index,
                )?;
                if let Some(formula) =
                    self.field_invariant_formula(&field.ty, &field_value, solver)?
                {
                    formulas.push(formula);
                }
            }
            branches.push(bool_conjoin(formulas));
        }
        let pattern = Pattern::new(&[&inv_app]);
        let body = bool_implies(inv_app.clone(), bool_disjoin(branches));
        solver.assert(ast::forall_const(&[&value], &[&pattern], &body));
        Ok(())
    }

    fn assert_patterned_forall(
        &self,
        solver: &Z3Solver,
        bounds: &[&dyn Ast],
        pattern_term: &dyn Ast,
        body: &Bool,
    ) {
        if bounds.is_empty() {
            solver.assert(body);
            return;
        }
        let pattern = Pattern::new(&[pattern_term]);
        solver.assert(ast::forall_const(bounds, &[&pattern], body));
    }

    fn field_invariant_formula(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        solver: &Z3Solver,
    ) -> Result<Option<Bool>, String> {
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
            | SpecTy::Usize => Ok(self.int_bounds(ty)?.map(|(lower, upper)| {
                bool_conjoin(vec![
                    self.int_term(value).ge(lower),
                    self.int_term(value).le(upper),
                ])
            })),
            SpecTy::TypeParam(_) => Ok(None),
            SpecTy::Seq(_) => Ok(None),
            SpecTy::Ref(inner) => {
                let composite = self.composite_encoding(ty, solver)?;
                let deref = self.project_composite_field(&composite, value, 0)?;
                let mut forms = vec![self.tag_formula(&composite, 0, value)?];
                if let Some(formula) = self.field_invariant_formula(inner, &deref, solver)? {
                    forms.push(formula);
                }
                Ok(Some(bool_conjoin(forms)))
            }
            SpecTy::Mut(inner) => {
                let composite = self.composite_encoding(ty, solver)?;
                let current = self.project_composite_field(&composite, value, 0)?;
                let mut forms = vec![self.tag_formula(&composite, 0, value)?];
                if let Some(formula) = self.field_invariant_formula(inner, &current, solver)? {
                    forms.push(formula);
                }
                Ok(Some(bool_conjoin(forms)))
            }
            SpecTy::Tuple(items) => {
                let composite = self.composite_encoding(ty, solver)?;
                let mut forms = vec![self.tag_formula(&composite, 0, value)?];
                for (index, item_ty) in items.iter().enumerate() {
                    let field = self.project_composite_field(&composite, value, index)?;
                    if let Some(formula) = self.field_invariant_formula(item_ty, &field, solver)? {
                        forms.push(formula);
                    }
                }
                Ok(Some(bool_conjoin(forms)))
            }
            SpecTy::Struct { name, args } => {
                let composite = self.composite_encoding(ty, solver)?;
                if name == "Ptr" {
                    return Ok(Some(self.tag_formula(&composite, 0, value)?));
                }
                let struct_def = self
                    .struct_defs
                    .borrow()
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown spec struct `{name}`"))?;
                let bindings = struct_def
                    .type_params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                let mut forms = vec![self.tag_formula(&composite, 0, value)?];
                for (index, field_ty) in struct_def.fields.iter().enumerate() {
                    let field = self.project_composite_field(&composite, value, index)?;
                    let field_ty = self.instantiate_named_field_ty(&field_ty.ty, &bindings)?;
                    if let Some(formula) =
                        self.field_invariant_formula(&field_ty, &field, solver)?
                    {
                        forms.push(formula);
                    }
                }
                Ok(Some(bool_conjoin(forms)))
            }
            SpecTy::Enum { name, args } => {
                let invariant = self
                    .named_invariant(
                        &SpecTy::Enum {
                            name: name.clone(),
                            args: args.clone(),
                        },
                        solver,
                    )?
                    .ok_or_else(|| format!("missing invariant predicate for `{name}`"))?;
                Ok(Some(
                    invariant
                        .apply(&[value.ast()])
                        .as_bool()
                        .expect("named invariant predicate"),
                ))
            }
        }
    }

    fn composite_ctor_specs(&self, ty: &SpecTy) -> Result<CtorSpecs, String> {
        match ty {
            SpecTy::Ref(inner) => Ok(vec![(
                String::new(),
                vec![
                    ("deref".to_owned(), (**inner).clone()),
                    ("ptr".to_owned(), ptr_spec_ty()),
                ],
            )]),
            SpecTy::Mut(inner) => Ok(vec![(
                String::new(),
                vec![
                    ("cur".to_owned(), (**inner).clone()),
                    ("fin".to_owned(), (**inner).clone()),
                    ("ptr".to_owned(), ptr_spec_ty()),
                ],
            )]),
            SpecTy::Tuple(items) => Ok(vec![(
                String::new(),
                items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| (format!("_{index}"), item.clone()))
                    .collect(),
            )]),
            SpecTy::Struct { name, args } => {
                let struct_def = self
                    .struct_defs
                    .borrow()
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown spec struct `{name}`"))?;
                if struct_def.type_params.len() != args.len() {
                    return Err(format!(
                        "spec struct `{name}` expects {} type arguments, found {}",
                        struct_def.type_params.len(),
                        args.len()
                    ));
                }
                let bindings = struct_def
                    .type_params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                Ok(vec![(
                    String::new(),
                    struct_def
                        .fields
                        .iter()
                        .map(|field| {
                            Ok((
                                field.name.clone(),
                                self.instantiate_named_field_ty(&field.ty, &bindings)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                )])
            }
            SpecTy::Enum { name, args } => self.named_ctor_specs(name, args),
            other => Err(format!(
                "expected composite-backed spec type, found {other:?}"
            )),
        }
    }

    fn named_ctor_specs(&self, name: &str, type_args: &[SpecTy]) -> Result<CtorSpecs, String> {
        let enum_def = self
            .enum_defs
            .borrow()
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown spec enum `{name}`"))?;
        if enum_def.type_params.len() != type_args.len() {
            return Err(format!(
                "spec enum `{name}` expects {} type arguments, found {}",
                enum_def.type_params.len(),
                type_args.len()
            ));
        }
        let bindings = enum_def
            .type_params
            .iter()
            .cloned()
            .zip(type_args.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        enum_def
            .ctors
            .into_iter()
            .map(|ctor| {
                Ok((
                    ctor.name,
                    ctor.fields
                        .into_iter()
                        .enumerate()
                        .map(|(index, field_ty)| {
                            Ok((
                                index.to_string(),
                                self.instantiate_named_field_ty(&field_ty, &bindings)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                ))
            })
            .collect()
    }

    fn instantiate_named_field_ty(
        &self,
        ty: &SpecTy,
        bindings: &BTreeMap<String, SpecTy>,
    ) -> Result<SpecTy, String> {
        match ty {
            SpecTy::Bool => Ok(SpecTy::Bool),
            SpecTy::RustTy => Ok(SpecTy::RustTy),
            SpecTy::Int => Ok(SpecTy::Int),
            SpecTy::IntLiteral => Ok(SpecTy::IntLiteral),
            SpecTy::I8 => Ok(SpecTy::I8),
            SpecTy::I16 => Ok(SpecTy::I16),
            SpecTy::I32 => Ok(SpecTy::I32),
            SpecTy::I64 => Ok(SpecTy::I64),
            SpecTy::Isize => Ok(SpecTy::Isize),
            SpecTy::U8 => Ok(SpecTy::U8),
            SpecTy::U16 => Ok(SpecTy::U16),
            SpecTy::U32 => Ok(SpecTy::U32),
            SpecTy::U64 => Ok(SpecTy::U64),
            SpecTy::Usize => Ok(SpecTy::Usize),
            SpecTy::Seq(inner) => Ok(SpecTy::Seq(Box::new(
                self.instantiate_named_field_ty(inner, bindings)?,
            ))),
            SpecTy::Tuple(items) => Ok(SpecTy::Tuple(
                items
                    .iter()
                    .map(|item| self.instantiate_named_field_ty(item, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            SpecTy::Struct { name, args } => Ok(SpecTy::Struct {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| self.instantiate_named_field_ty(arg, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            SpecTy::Enum { name, args } => Ok(SpecTy::Enum {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| self.instantiate_named_field_ty(arg, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            SpecTy::TypeParam(name) => bindings
                .get(name)
                .cloned()
                .ok_or_else(|| format!("unbound spec type parameter `{name}` in enum encoding")),
            SpecTy::Ref(inner) => Ok(SpecTy::Ref(Box::new(
                self.instantiate_named_field_ty(inner, bindings)?,
            ))),
            SpecTy::Mut(inner) => Ok(SpecTy::Mut(Box::new(
                self.instantiate_named_field_ty(inner, bindings)?,
            ))),
        }
    }

    fn sort_for_spec_ty(&self, ty: &SpecTy) -> Result<Sort, String> {
        match ty {
            SpecTy::Seq(_) => Ok(self.seq_value_sort.clone()),
            SpecTy::TypeParam(_) => Ok(self.value_sort.clone()),
            _ => Ok(self.value_sort.clone()),
        }
    }

    fn type_name(&self, ty: &SpecTy) -> String {
        fn sanitize(raw: &str) -> String {
            raw.chars()
                .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
                .collect()
        }

        match ty {
            SpecTy::Bool => "bool".to_owned(),
            SpecTy::RustTy => "rust_ty".to_owned(),
            SpecTy::Int => "int".to_owned(),
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
            SpecTy::Tuple(items) => format!(
                "tuple_{}",
                items
                    .iter()
                    .map(|item| self.type_name(item))
                    .collect::<Vec<_>>()
                    .join("_")
            ),
            SpecTy::Struct { name, args } => self.instantiated_named_type_name(name, args),
            SpecTy::Enum { name, args } => self.instantiated_named_type_name(name, args),
            SpecTy::Seq(inner) => format!("seq_{}", self.type_name(inner)),
            SpecTy::Ref(inner) => format!("ref_{}", self.type_name(inner)),
            SpecTy::Mut(inner) => format!("mut_{}", self.type_name(inner)),
            SpecTy::TypeParam(name) => format!("typeparam_{}", sanitize(name)),
        }
    }

    fn enum_family_name(&self, name: &str) -> String {
        format!("enum_{}", self.sanitize_name(name))
    }

    fn instantiated_named_type_name(&self, name: &str, args: &[SpecTy]) -> String {
        let base = self.enum_family_name(name);
        if args.is_empty() {
            return base;
        }
        format!(
            "{}_{}",
            base,
            args.iter()
                .map(|arg| self.type_name(arg))
                .collect::<Vec<_>>()
                .join("_")
        )
    }

    fn sanitize_name(&self, raw: &str) -> String {
        raw.chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect()
    }

    fn pointer_sized_int_bounds(&self, signed: bool) -> Result<(Int, Int), String> {
        let bits = self.pointer_width_bits;
        if signed {
            let lower = -(1_i128 << (bits - 1));
            let upper = (1_i128 << (bits - 1)) - 1;
            let lower = Int::from_str(&lower.to_string())
                .map_err(|()| "invalid isize lower bound".to_owned())?;
            let upper = Int::from_str(&upper.to_string())
                .map_err(|()| "invalid isize upper bound".to_owned())?;
            Ok((lower, upper))
        } else {
            let upper = (1_u128 << bits) - 1;
            let upper = Int::from_str(&upper.to_string())
                .map_err(|()| "invalid usize upper bound".to_owned())?;
            Ok((Int::from_u64(0), upper))
        }
    }
}

fn bool_conjoin(forms: Vec<Bool>) -> Bool {
    if forms.is_empty() {
        Bool::from_bool(true)
    } else {
        let refs = forms.iter().collect::<Vec<_>>();
        Bool::and(&refs)
    }
}

fn bool_disjoin(forms: Vec<Bool>) -> Bool {
    if forms.is_empty() {
        Bool::from_bool(false)
    } else {
        let refs = forms.iter().collect::<Vec<_>>();
        Bool::or(&refs)
    }
}

fn bool_implies(lhs: Bool, rhs: Bool) -> Bool {
    lhs.implies(rhs)
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
    with_z3_solver(|solver| solver.reset());
}

pub(crate) fn with_z3_solver<T>(f: impl FnOnce(&Z3Solver) -> T) -> T {
    Z3_SOLVER.with(|solver| f(&solver.borrow()))
}

pub(crate) fn with_z3_context<T>(f: impl FnOnce() -> T + Send + Sync) -> T
where
    T: Send + Sync,
{
    z3::with_z3_config(&Config::new(), f)
}

pub(crate) fn with_z3_deadline<T>(budget: Duration, f: impl FnOnce() -> T) -> (T, bool) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::StructFieldTy;
    use z3::{SatResult, SortKind};

    fn with_test_solver<T>(f: impl FnOnce(&Solver, &Z3Solver) -> T) -> T {
        let solver = Solver::new(64);
        with_z3_solver(|z3_solver| f(&solver, z3_solver))
    }

    #[test]
    fn thread_local_solver_distinguishes_sat_from_unsat() {
        rebuild_z3_solver();
        let x = Int::new_const("x");
        let sat = with_z3_solver(|solver| {
            solver.push();
            solver.assert(x.eq(1));
            let result = solver.check();
            solver.pop(1);
            result
        });
        assert_eq!(sat, SatResult::Sat);

        let unsat = with_z3_solver(|solver| {
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
    fn z3_context_solver_distinguishes_sat_from_unsat() {
        let result = with_z3_context(|| {
            rebuild_z3_solver();
            let x = Int::new_const("x");
            let sat = with_z3_solver(|solver| {
                solver.push();
                solver.assert(x.eq(1));
                let result = solver.check();
                solver.pop(1);
                result
            });
            let unsat = with_z3_solver(|solver| {
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
    fn encodes_all_types_in_shared_value_sort() {
        with_test_solver(|solver, z3_solver| {
            let bool_encoding = solver
                .type_encoding(&SpecTy::Bool, z3_solver)
                .expect("bool encoding");
            let int_encoding = solver
                .type_encoding(&SpecTy::I32, z3_solver)
                .expect("int encoding");
            let tuple_encoding = solver
                .type_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), z3_solver)
                .expect("tuple encoding");
            solver.register_struct_def(StructDef {
                name: "Pair".to_owned(),
                type_params: Vec::new(),
                fields: vec![
                    StructFieldTy {
                        name: "flag".to_owned(),
                        ty: SpecTy::Bool,
                    },
                    StructFieldTy {
                        name: "count".to_owned(),
                        ty: SpecTy::I32,
                    },
                ],
                invariant: None,
            });
            let struct_encoding = solver
                .type_encoding(
                    &SpecTy::Struct {
                        name: "Pair".to_owned(),
                        args: Vec::new(),
                    },
                    z3_solver,
                )
                .expect("struct encoding");

            assert!(matches!(bool_encoding.kind, TypeEncodingKind::Bool));
            assert!(matches!(int_encoding.kind, TypeEncodingKind::Int));
            assert!(matches!(
                tuple_encoding.kind,
                TypeEncodingKind::Composite(_)
            ));
            assert!(matches!(
                struct_encoding.kind,
                TypeEncodingKind::Composite(_)
            ));
            assert_eq!(solver.value_sort().kind(), SortKind::Uninterpreted);
        });
    }

    #[test]
    fn composite_constructors_are_uninterpreted_function_symbols() {
        with_test_solver(|solver, z3_solver| {
            let _ = solver
                .type_encoding(&SpecTy::Bool, z3_solver)
                .expect("bool encoding");
            let _ = solver
                .type_encoding(&SpecTy::I32, z3_solver)
                .expect("int encoding");
            let tuple_encoding = solver
                .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), z3_solver)
                .expect("tuple encoding");
            let tuple_ctor = tuple_encoding
                .single_constructor()
                .expect("single constructor");

            assert_eq!(tuple_encoding.constructors.len(), 1);
            assert_eq!(tuple_ctor.name, "mk_tuple_bool_i32");
            assert_eq!(tuple_ctor.fields.len(), 2);

            let tuple_value = tuple_ctor.symbol.apply(&[
                &solver.bool_encoding.boxed.apply(&[&Bool::from_bool(true)]),
                &solver.int_encoding.boxed.apply(&[&Int::from_i64(3)]),
            ]);
            assert_eq!(tuple_value.decl().name(), tuple_ctor.name);
            assert_eq!(tuple_value.children().len(), 2);
            assert_eq!(tuple_value.get_sort().kind(), SortKind::Uninterpreted);
        });
    }

    #[test]
    fn primitive_terms_unwrap_boxed_values_syntactically() {
        with_test_solver(|solver, z3_solver| {
            let _ = solver
                .type_encoding(&SpecTy::Bool, z3_solver)
                .expect("bool encoding");
            let _ = solver
                .type_encoding(&SpecTy::I32, z3_solver)
                .expect("int encoding");
            let boxed_bool = solver.bool_value(true);
            assert_eq!(solver.bool_term(&boxed_bool).to_string(), "true");

            let boxed_int = solver.int_value(42);
            assert_eq!(solver.int_term(&boxed_int).to_string(), "42");
        });
    }

    #[test]
    fn primitive_encodings_keep_solver_consistent() {
        with_test_solver(|solver, z3_solver| {
            let _ = solver
                .type_encoding(&SpecTy::Bool, z3_solver)
                .expect("bool encoding");
            let _ = solver
                .type_encoding(&SpecTy::I32, z3_solver)
                .expect("int encoding");

            assert_eq!(z3_solver.check(), SatResult::Sat);
        });
    }

    #[test]
    fn pure_function_declarations_are_owned_by_solver() {
        let solver = Solver::new(64);
        solver
            .declare_pure_fn("id", &[SpecTy::I32], &SpecTy::I32)
            .expect("declare pure function");
        let mut next = 0;
        let params = solver
            .pure_fn_params("id", &[("x".to_owned(), SpecTy::I32)], &mut |hint| {
                next += 1;
                format!("{hint}_{next}")
            })
            .expect("pure function params");
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].0, "x");
        solver
            .define_pure_fn("id", &[params[0].1.clone()], &params[0].1)
            .expect("define pure function");

        let value = solver
            .apply_pure_fn("id", &[solver.int_value(5)])
            .expect("apply pure function")
            .expect("known pure function");
        assert_eq!(value.dynamic().decl().name().to_string(), "pure_fn_id");
        assert!(
            solver
                .apply_pure_fn("unknown", &[])
                .expect("unknown pure function")
                .is_none()
        );
    }

    #[test]
    fn sequence_literal_lengths_stay_ground() {
        let solver = Solver::new(64);
        let seq = solver.seq_literal_value(&[solver.int_value(0), solver.int_value(1)]);
        let length = solver.seq_len_int(&seq).expect("sequence length");
        assert_eq!(length.as_i64(), Some(2));
    }

    #[test]
    fn ground_sequence_equality_ignores_concat_shape() {
        let solver = Solver::new(64);
        let seq_ty = SpecTy::Seq(Box::new(SpecTy::I32));
        let lhs_tail = solver
            .lower_binary_value(
                BinaryOp::Concat,
                &seq_ty,
                &solver.seq_literal_value(&[solver.int_value(0)]),
                &solver.seq_literal_value(&[]),
            )
            .expect("tail concat");
        let lhs = solver
            .lower_binary_value(
                BinaryOp::Concat,
                &seq_ty,
                &solver.seq_literal_value(&[solver.int_value(1)]),
                &lhs_tail,
            )
            .expect("lhs concat");
        let rhs = solver.seq_literal_value(&[solver.int_value(1), solver.int_value(0)]);
        let equal = solver
            .eq_for_spec_ty(&seq_ty, &lhs, &rhs)
            .expect("sequence equality");
        assert_eq!(equal.as_bool(), Some(true));
    }

    #[test]
    fn known_structural_composites_project_and_tag_syntactically() {
        with_test_solver(|solver, z3_solver| {
            let _ = solver
                .type_encoding(&SpecTy::Bool, z3_solver)
                .expect("bool encoding");
            let _ = solver
                .type_encoding(&SpecTy::I32, z3_solver)
                .expect("int encoding");
            let tuple_encoding = solver
                .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), z3_solver)
                .expect("tuple encoding");
            let tuple_ctor = tuple_encoding
                .single_constructor()
                .expect("single constructor");
            let flag = Bool::new_const("flag");
            let count = Int::new_const("count");
            let tuple = tuple_ctor.symbol.apply(&[
                &solver.bool_encoding.boxed.apply(&[&flag]),
                &solver.int_encoding.boxed.apply(&[&count]),
            ]);

            assert_eq!(
                solver
                    .project_composite_field(&tuple_encoding, &SymValue::new(tuple.clone()), 0)
                    .expect("flag field")
                    .dynamic(),
                &solver.bool_encoding.boxed.apply(&[&flag])
            );
            assert_eq!(
                solver
                    .project_composite_field(&tuple_encoding, &SymValue::new(tuple.clone()), 1)
                    .expect("count field")
                    .dynamic(),
                &solver.int_encoding.boxed.apply(&[&count])
            );

            assert_eq!(
                solver
                    .tag_formula(&tuple_encoding, 0, &SymValue::new(tuple))
                    .expect("tuple tag")
                    .simplify()
                    .as_bool(),
                Some(true)
            );
        });
    }

    #[test]
    fn opaque_structural_composites_do_not_gain_eta_axioms() {
        with_test_solver(|solver, z3_solver| {
            let _ = solver
                .type_encoding(&SpecTy::Bool, z3_solver)
                .expect("bool encoding");
            let _ = solver
                .type_encoding(&SpecTy::I32, z3_solver)
                .expect("int encoding");
            let tuple_encoding = solver
                .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), z3_solver)
                .expect("tuple encoding");
            let tuple_ctor = tuple_encoding
                .single_constructor()
                .expect("single constructor");
            let opaque_tuple = Dynamic::new_const("opaque_tuple", solver.value_sort());
            let reconstructed = tuple_ctor.symbol.apply(&[
                &tuple_ctor.fields[0].inverse.apply(&[&opaque_tuple]),
                &tuple_ctor.fields[1].inverse.apply(&[&opaque_tuple]),
            ]);

            z3_solver.push();
            z3_solver.assert(reconstructed.eq(&opaque_tuple).not());
            assert_eq!(z3_solver.check(), SatResult::Sat);
            z3_solver.pop(1);
        });
    }

    #[test]
    fn composite_symbols_follow_verifast_style_naming() {
        with_test_solver(|solver, z3_solver| {
            let tuple_encoding = solver
                .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), z3_solver)
                .expect("tuple encoding");
            let tuple_ctor = tuple_encoding
                .single_constructor()
                .expect("single constructor");

            let tag_name = tuple_encoding.tag_function.name();
            assert!(tag_name.starts_with("ctortag"));
            assert!(
                tag_name["ctortag".len()..]
                    .chars()
                    .all(|ch| ch.is_ascii_digit())
            );

            for field in &tuple_ctor.fields {
                assert!(field.inverse.name().starts_with("ctorinv"));
            }
        });
    }
}
