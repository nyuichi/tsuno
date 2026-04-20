use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::str::FromStr;

use crate::spec::{BinaryOp, EnumDef, SpecTy, StructTy, UnaryOp};
use z3::ast::{self, Ast, Bool, Dynamic, Int};
use z3::{FuncDecl, Pattern, Solver, Sort, Symbol};

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
- Named spec types (`SpecTy::Named`, i.e. ghost enums such as `List<T>`) reuse
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

Named spec types also get a per-instantiation invariant predicate:

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
`RecFuncDecl`. This file only defines the value-level constructor/tag/invariant
encoding that those recursive definitions refer to.
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
pub(crate) struct TypeEncoding {
    pub(crate) kind: TypeEncodingKind,
}

#[derive(Debug)]
pub(crate) enum TypeEncodingKind {
    Bool,
    Int,
    Composite(Rc<CompositeEncoding>),
}

#[derive(Debug)]
pub(crate) struct PrimitiveEncoding {
    pub(crate) boxed: FuncDecl,
    pub(crate) unboxed: FuncDecl,
}

#[derive(Debug)]
pub(crate) struct CompositeEncoding {
    pub(crate) tag_function: FuncDecl,
    pub(crate) constructors: Vec<Rc<ConstructorEncoding>>,
    pub(crate) invariant: Option<Rc<FuncDecl>>,
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

impl CompositeEncoding {
    pub(crate) fn single_constructor(&self) -> Result<&ConstructorEncoding, String> {
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
pub(crate) struct ConstructorEncoding {
    pub(crate) name: String,
    pub(crate) symbol: FuncDecl,
    pub(crate) fields: Vec<FieldEncoding>,
    pub(crate) tag: Int,
}

#[derive(Debug)]
pub(crate) struct FieldEncoding {
    pub(crate) inverse: FuncDecl,
    pub(crate) ty: SpecTy,
}

type CtorFields = Vec<(String, SpecTy)>;
type CtorSpecs = Vec<(String, CtorFields)>;

pub(crate) struct ValueEncoder {
    pointer_width_bits: u64,
    value_sort: Sort,
    bool_encoding: Rc<PrimitiveEncoding>,
    int_encoding: Rc<PrimitiveEncoding>,
    primitive_axioms_asserted: Cell<bool>,
    next_subtype_id: Cell<u32>,
    next_ctor_tag: Cell<u32>,
    enum_defs: RefCell<BTreeMap<String, EnumDef>>,
    enum_family_encodings: RefCell<BTreeMap<String, Rc<EnumFamilyEncoding>>>,
    type_encodings: RefCell<BTreeMap<SpecTy, Rc<TypeEncoding>>>,
    asserted_type_axioms: RefCell<BTreeSet<SpecTy>>,
}

impl ValueEncoder {
    pub(crate) fn new(pointer_width_bits: u64) -> Self {
        let value_sort = Sort::uninterpreted(Symbol::String("value".to_owned()));
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
            bool_encoding,
            int_encoding,
            primitive_axioms_asserted: Cell::new(false),
            next_subtype_id: Cell::new(0),
            next_ctor_tag: Cell::new(0),
            enum_defs: RefCell::new(BTreeMap::new()),
            enum_family_encodings: RefCell::new(BTreeMap::new()),
            type_encodings: RefCell::new(BTreeMap::new()),
            asserted_type_axioms: RefCell::new(BTreeSet::new()),
        }
    }

    pub(crate) fn reset_solver_state(&self) {
        self.primitive_axioms_asserted.set(false);
        self.asserted_type_axioms.borrow_mut().clear();
    }

    pub(crate) fn register_enum_def(&self, def: EnumDef) {
        self.enum_defs.borrow_mut().insert(def.name.clone(), def);
    }

    pub(crate) fn value_sort(&self) -> &Sort {
        &self.value_sort
    }

    pub(crate) fn type_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<TypeEncoding>, String> {
        self.ensure_primitive_axioms(solver);
        if let Some(encoding) = self.type_encodings.borrow().get(ty).cloned() {
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

    pub(crate) fn composite_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<CompositeEncoding>, String> {
        let encoding = self.type_encoding(ty, solver)?;
        match &encoding.kind {
            TypeEncodingKind::Composite(encoding) => Ok(encoding.clone()),
            _ => Err(format!("expected composite-backed spec type, found {ty:?}")),
        }
    }

    pub(crate) fn named_invariant(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Option<Rc<FuncDecl>>, String> {
        let composite = self.composite_encoding(ty, solver)?;
        Ok(composite.invariant.clone())
    }

    pub(crate) fn wrap_bool(&self, value: &Bool) -> SymValue {
        SymValue::new(self.bool_encoding.boxed.apply(&[value]))
    }

    pub(crate) fn wrap_int(&self, value: &Int) -> SymValue {
        SymValue::new(self.int_encoding.boxed.apply(&[value]))
    }

    pub(crate) fn bool_value(&self, value: bool) -> SymValue {
        self.wrap_bool(&Bool::from_bool(value))
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

    pub(crate) fn eq_for_spec_ty(
        &self,
        ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        solver: &Solver,
    ) -> Result<Bool, String> {
        let encoding = self.type_encoding(ty, solver)?;
        Ok(match &encoding.kind {
            TypeEncodingKind::Bool => self.bool_term(lhs).eq(self.bool_term(rhs)),
            TypeEncodingKind::Int => self.int_term(lhs).eq(self.int_term(rhs)),
            TypeEncodingKind::Composite(_) => lhs.dynamic().eq(rhs.dynamic()),
        })
    }

    pub(crate) fn lower_unary_value(&self, op: UnaryOp, value: &SymValue) -> SymValue {
        match op {
            UnaryOp::Not => self.wrap_bool(&self.bool_term(value).not()),
            UnaryOp::Neg => self.wrap_int(&(Int::from_i64(0) - self.int_term(value))),
        }
    }

    pub(crate) fn lower_binary_value(
        &self,
        op: BinaryOp,
        lhs_ty: &SpecTy,
        lhs: &SymValue,
        rhs: &SymValue,
        solver: &Solver,
    ) -> Result<SymValue, String> {
        Ok(match op {
            BinaryOp::Eq => self.wrap_bool(&self.eq_for_spec_ty(lhs_ty, lhs, rhs, solver)?),
            BinaryOp::Ne => self.wrap_bool(&self.eq_for_spec_ty(lhs_ty, lhs, rhs, solver)?.not()),
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
        })
    }

    pub(crate) fn construct_composite(
        &self,
        ty: &SpecTy,
        fields: &[SymValue],
        solver: &Solver,
    ) -> Result<SymValue, String> {
        self.construct_composite_ctor(ty, 0, fields, solver)
    }

    pub(crate) fn construct_composite_ctor(
        &self,
        ty: &SpecTy,
        ctor_index: usize,
        fields: &[SymValue],
        solver: &Solver,
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

    pub(crate) fn project_field(
        &self,
        ty: &SpecTy,
        value: &SymValue,
        index: usize,
        solver: &Solver,
    ) -> Result<SymValue, String> {
        let composite = self.composite_encoding(ty, solver)?;
        self.project_composite_field(&composite, value, index)
    }

    pub(crate) fn project_composite_field(
        &self,
        composite: &CompositeEncoding,
        value: &SymValue,
        index: usize,
    ) -> Result<SymValue, String> {
        self.project_composite_ctor_field(composite, 0, value, index)
    }

    pub(crate) fn project_composite_ctor_field(
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

    pub(crate) fn tag_formula(
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

    pub(crate) fn int_bounds(&self, ty: &SpecTy) -> Result<Option<(Int, Int)>, String> {
        Ok(Some(match ty {
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
        let kind = match ty {
            SpecTy::Bool => TypeEncodingKind::Bool,
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
            | SpecTy::Usize => TypeEncodingKind::Int,
            SpecTy::Tuple(_)
            | SpecTy::Struct(_)
            | SpecTy::Named { .. }
            | SpecTy::Ref(_)
            | SpecTy::Mut(_) => TypeEncodingKind::Composite(self.build_composite_encoding(ty)?),
            SpecTy::TypeParam(name) => {
                return Err(format!(
                    "unresolved spec type parameter `{name}` reached value encoding"
                ));
            }
        };
        Ok(Rc::new(TypeEncoding { kind }))
    }

    fn build_composite_encoding(&self, ty: &SpecTy) -> Result<Rc<CompositeEncoding>, String> {
        if let SpecTy::Named { name, args } = ty {
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
            .map(|(ctor_name, fields)| {
                let constructor_name = if ctor_name.is_empty() {
                    format!("mk_{sort_name}")
                } else {
                    format!("mk_{sort_name}_{ctor_name}")
                };
                let constructor_tag = Int::from_u64(u64::from(self.next_ctor_tag.get()));
                self.next_ctor_tag.set(self.next_ctor_tag.get() + 1);
                let domain_sorts = fields.iter().map(|_| &self.value_sort).collect::<Vec<_>>();
                let constructor_symbol =
                    FuncDecl::new(constructor_name.as_str(), &domain_sorts, &self.value_sort);
                let fields = fields
                    .into_iter()
                    .map(|(label, field_ty)| FieldEncoding {
                        inverse: FuncDecl::new(
                            if ctor_name.is_empty() {
                                format!("ctorinv_{sort_name}_{label}")
                            } else {
                                format!("ctorinv_{sort_name}_{ctor_name}_{label}")
                            },
                            &[&self.value_sort],
                            &self.value_sort,
                        ),
                        ty: field_ty,
                    })
                    .collect::<Vec<_>>();
                Rc::new(ConstructorEncoding {
                    name: constructor_name,
                    symbol: constructor_symbol,
                    fields,
                    tag: constructor_tag,
                })
            })
            .collect::<Vec<_>>();
        let composite = Rc::new(CompositeEncoding {
            tag_function,
            constructors,
            invariant: matches!(ty, SpecTy::Named { .. }).then(|| {
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
            .map(|(family_ctor, (_ctor_name, fields))| {
                let field_count = fields.len();
                let domain_sorts = (0..field_count)
                    .map(|_| &self.value_sort)
                    .collect::<Vec<_>>();
                Rc::new(ConstructorEncoding {
                    name: family_ctor.symbol_name.clone(),
                    symbol: FuncDecl::new(
                        family_ctor.symbol_name.as_str(),
                        &domain_sorts,
                        &self.value_sort,
                    ),
                    fields: fields
                        .into_iter()
                        .enumerate()
                        .map(|(index, (_label, ty))| FieldEncoding {
                            inverse: FuncDecl::new(
                                family_ctor.inverse_names[index].as_str(),
                                &[&self.value_sort],
                                &self.value_sort,
                            ),
                            ty,
                        })
                        .collect(),
                    tag: Int::from_u64(u64::from(family_ctor.tag_value)),
                })
            })
            .collect::<Vec<_>>();

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
        solver: &Solver,
    ) -> Result<(), String> {
        match &encoding.kind {
            TypeEncodingKind::Bool | TypeEncodingKind::Int => Ok(()),
            TypeEncodingKind::Composite(composite) => {
                if matches!(ty, SpecTy::Named { .. }) {
                    self.assert_composite_axioms(composite, solver);
                    self.assert_named_invariant_axioms(ty, composite, solver)?;
                }
                Ok(())
            }
        }
    }

    fn ensure_primitive_axioms(&self, solver: &Solver) {
        let _ = solver;
        if self.primitive_axioms_asserted.get() {
            return;
        }
        self.primitive_axioms_asserted.set(true);
    }

    fn assert_composite_axioms(&self, composite: &CompositeEncoding, solver: &Solver) {
        for ctor in &composite.constructors {
            let args = ctor
                .fields
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    Dynamic::new_const(format!("{}_arg_{index}", ctor.name), &self.value_sort)
                })
                .collect::<Vec<_>>();
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
    }

    fn assert_named_invariant_axioms(
        &self,
        ty: &SpecTy,
        composite: &CompositeEncoding,
        solver: &Solver,
    ) -> Result<(), String> {
        let Some(invariant) = &composite.invariant else {
            return Ok(());
        };

        for ctor in &composite.constructors {
            let args = ctor
                .fields
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    Dynamic::new_const(format!("{}_inv_arg_{index}", ctor.name), &self.value_sort)
                })
                .collect::<Vec<_>>();
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
        solver: &Solver,
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
        solver: &Solver,
    ) -> Result<Option<Bool>, String> {
        match ty {
            SpecTy::Bool => Ok(None),
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
            | SpecTy::Usize => Ok(self.int_bounds(ty)?.map(|(lower, upper)| {
                bool_conjoin(vec![
                    self.int_term(value).ge(lower),
                    self.int_term(value).le(upper),
                ])
            })),
            SpecTy::Named { name, args } => {
                let invariant = self
                    .named_invariant(
                        &SpecTy::Named {
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
            other => Err(format!(
                "unsupported spec enum field type in invariant encoding: {other:?}"
            )),
        }
    }

    fn composite_ctor_specs(&self, ty: &SpecTy) -> Result<CtorSpecs, String> {
        match ty {
            SpecTy::Ref(inner) => Ok(vec![(
                String::new(),
                vec![("deref".to_owned(), (**inner).clone())],
            )]),
            SpecTy::Mut(inner) => Ok(vec![(
                String::new(),
                vec![
                    ("cur".to_owned(), (**inner).clone()),
                    ("fin".to_owned(), (**inner).clone()),
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
            SpecTy::Struct(StructTy { fields, .. }) => Ok(vec![(
                String::new(),
                fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty.clone()))
                    .collect(),
            )]),
            SpecTy::Named { name, args } => self.named_ctor_specs(name, args),
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
            SpecTy::Tuple(items) => Ok(SpecTy::Tuple(
                items
                    .iter()
                    .map(|item| self.instantiate_named_field_ty(item, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            SpecTy::Struct(struct_ty) => Ok(SpecTy::Struct(StructTy {
                name: struct_ty.name.clone(),
                fields: struct_ty
                    .fields
                    .iter()
                    .map(|field| {
                        Ok(crate::spec::StructFieldTy {
                            name: field.name.clone(),
                            ty: self.instantiate_named_field_ty(&field.ty, bindings)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            })),
            SpecTy::Named { name, args } => Ok(SpecTy::Named {
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
            SpecTy::Ref(_) | SpecTy::Mut(_) => Err(format!(
                "unsupported spec enum field type in value encoding: {ty:?}"
            )),
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
            SpecTy::Struct(struct_ty) => format!("struct_{}", sanitize(&struct_ty.name)),
            SpecTy::Named { name, args } => self.instantiated_named_type_name(name, args),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::{StructFieldTy, StructTy};
    use z3::{SatResult, SortKind};

    #[test]
    fn encodes_all_types_in_shared_value_sort() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);

        let bool_encoding = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let int_encoding = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .type_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");
        let struct_encoding = encoder
            .type_encoding(
                &SpecTy::Struct(StructTy {
                    name: "Pair".to_owned(),
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
                }),
                &solver,
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
        assert_eq!(encoder.value_sort().kind(), SortKind::Uninterpreted);
    }

    #[test]
    fn composite_constructors_are_uninterpreted_function_symbols() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let _ = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let _ = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");
        let tuple_ctor = tuple_encoding
            .single_constructor()
            .expect("single constructor");

        assert_eq!(tuple_encoding.constructors.len(), 1);
        assert_eq!(tuple_ctor.name, "mk_tuple_bool_i32");
        assert_eq!(tuple_ctor.fields.len(), 2);

        let tuple_value = tuple_ctor.symbol.apply(&[
            &encoder.bool_encoding.boxed.apply(&[&Bool::from_bool(true)]),
            &encoder.int_encoding.boxed.apply(&[&Int::from_i64(3)]),
        ]);
        assert_eq!(tuple_value.decl().name(), tuple_ctor.name);
        assert_eq!(tuple_value.children().len(), 2);
        assert_eq!(tuple_value.get_sort().kind(), SortKind::Uninterpreted);
    }

    #[test]
    fn primitive_terms_unwrap_boxed_values_syntactically() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let _ = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let _ = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let boxed_bool = encoder.bool_value(true);
        assert_eq!(encoder.bool_term(&boxed_bool).to_string(), "true");

        let boxed_int = encoder.int_value(42);
        assert_eq!(encoder.int_term(&boxed_int).to_string(), "42");
    }

    #[test]
    fn primitive_encodings_keep_solver_consistent() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        let _ = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let _ = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");

        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn known_structural_composites_project_and_tag_syntactically() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let _ = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let _ = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");
        let tuple_ctor = tuple_encoding
            .single_constructor()
            .expect("single constructor");
        let flag = Bool::new_const("flag");
        let count = Int::new_const("count");
        let tuple = tuple_ctor.symbol.apply(&[
            &encoder.bool_encoding.boxed.apply(&[&flag]),
            &encoder.int_encoding.boxed.apply(&[&count]),
        ]);

        assert_eq!(
            encoder
                .project_composite_field(&tuple_encoding, &SymValue::new(tuple.clone()), 0)
                .expect("flag field")
                .dynamic(),
            &encoder.bool_encoding.boxed.apply(&[&flag])
        );
        assert_eq!(
            encoder
                .project_composite_field(&tuple_encoding, &SymValue::new(tuple.clone()), 1)
                .expect("count field")
                .dynamic(),
            &encoder.int_encoding.boxed.apply(&[&count])
        );

        assert_eq!(
            encoder
                .tag_formula(&tuple_encoding, 0, &SymValue::new(tuple))
                .expect("tuple tag")
                .simplify()
                .as_bool(),
            Some(true)
        );
    }

    #[test]
    fn opaque_structural_composites_do_not_gain_eta_axioms() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let _ = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let _ = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");
        let tuple_ctor = tuple_encoding
            .single_constructor()
            .expect("single constructor");
        let opaque_tuple = Dynamic::new_const("opaque_tuple", encoder.value_sort());
        let reconstructed = tuple_ctor.symbol.apply(&[
            &tuple_ctor.fields[0].inverse.apply(&[&opaque_tuple]),
            &tuple_ctor.fields[1].inverse.apply(&[&opaque_tuple]),
        ]);

        solver.push();
        solver.assert(reconstructed.eq(&opaque_tuple).not());
        assert_eq!(solver.check(), SatResult::Sat);
        solver.pop(1);
    }

    #[test]
    fn composite_symbols_follow_verifast_style_naming() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let tuple_encoding = encoder
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
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
    }
}
