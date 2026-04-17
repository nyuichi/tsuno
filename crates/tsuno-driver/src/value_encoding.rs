#![allow(dead_code)]

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::rc::Rc;
use std::str::FromStr;

use crate::spec::{SpecTy, StructTy};
use z3::ast::{Ast, Dynamic, Int};
use z3::datatype_builder::{DatatypeAccessor, create_datatypes};
use z3::{DatatypeBuilder, FuncDecl, RecFuncDecl, Solver, Sort};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SymValue {
    Bool(PrimitiveValue),
    Int(PrimitiveValue),
    Inductive(InductiveValue),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PrimitiveValue {
    pub(crate) ast: Dynamic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InductiveValue {
    pub(crate) ast: Dynamic,
}

#[derive(Debug)]
pub(crate) struct TypeEncoding {
    pub(crate) sort: Sort,
    pub(crate) kind: TypeEncodingKind,
    pub(crate) semantics: TypeSemantics,
}

#[derive(Debug)]
pub(crate) enum TypeEncodingKind {
    Bool(Rc<PrimitiveEncoding>),
    Int(Rc<PrimitiveEncoding>),
    Inductive(Rc<InductiveEncoding>),
}

#[derive(Debug)]
pub(crate) struct PrimitiveEncoding {
    pub(crate) boxed: FuncDecl,
    pub(crate) unboxed: FuncDecl,
    pub(crate) tag: Int,
}

#[derive(Debug)]
pub(crate) struct InductiveEncoding {
    pub(crate) constructor_name: String,
    pub(crate) field_labels: Vec<String>,
    pub(crate) constructor: RecFuncDecl,
    pub(crate) accessors: Vec<RecFuncDecl>,
    pub(crate) fields: Vec<Rc<TypeEncoding>>,
    pub(crate) tag: Int,
}

#[derive(Debug, Clone)]
pub(crate) enum TypeSemantics {
    Bool,
    Int { bounds: Option<(Int, Int)> },
    Ref,
    Mut,
    Tuple,
    Struct,
}

pub(crate) struct ValueEncoder {
    pointer_width_bits: u64,
    value_sort: Sort,
    tag_function: RecFuncDecl,
    generic_ctor: FuncDecl,
    generic_ctor_fields: FuncDecl,
    list_nil: FuncDecl,
    list_cons: FuncDecl,
    list_head: FuncDecl,
    list_tail: FuncDecl,
    bool_encoding: Rc<PrimitiveEncoding>,
    int_encoding: Rc<PrimitiveEncoding>,
    next_ctor_tag: Cell<u32>,
    type_encodings: RefCell<BTreeMap<SpecTy, Rc<TypeEncoding>>>,
}

impl ValueEncoder {
    pub(crate) fn new(pointer_width_bits: u64) -> Self {
        let value_builder = DatatypeBuilder::new("inductive")
            .variant(
                "boolbox",
                vec![("payload", DatatypeAccessor::sort(Sort::bool()))],
            )
            .variant(
                "intbox",
                vec![("payload", DatatypeAccessor::sort(Sort::int()))],
            )
            .variant(
                "ctorbox",
                vec![
                    ("tag", DatatypeAccessor::sort(Sort::int())),
                    ("fields", DatatypeAccessor::datatype("inductive_list")),
                ],
            );
        let list_builder = DatatypeBuilder::new("inductive_list")
            .variant("nil", vec![])
            .variant(
                "cons",
                vec![
                    ("head", DatatypeAccessor::datatype("inductive")),
                    ("tail", DatatypeAccessor::datatype("inductive_list")),
                ],
            );
        let mut datatypes = create_datatypes(vec![value_builder, list_builder]);
        let value_datatype = datatypes.remove(0);
        let list_datatype = datatypes.remove(0);

        let value_sort = value_datatype.sort;
        let mut value_variants = value_datatype.variants;
        let bool_variant = value_variants.remove(0);
        let int_variant = value_variants.remove(0);
        let ctor_variant = value_variants.remove(0);
        let mut list_variants = list_datatype.variants;
        let nil_variant = list_variants.remove(0);
        let cons_variant = list_variants.remove(0);
        let bool_tag = Int::from_u64(0);
        let int_tag = Int::from_u64(1);

        let bool_boxed = bool_variant.constructor;
        let bool_tester = bool_variant.tester;
        let bool_unboxed = bool_variant
            .accessors
            .into_iter()
            .next()
            .expect("bool accessor");
        let int_boxed = int_variant.constructor;
        let int_tester = int_variant.tester;
        let int_unboxed = int_variant
            .accessors
            .into_iter()
            .next()
            .expect("int accessor");
        let ctor_constructor = ctor_variant.constructor;
        let mut ctor_accessors = ctor_variant.accessors.into_iter();
        let ctor_tag_accessor = ctor_accessors.next().expect("ctor tag accessor");
        let ctor_fields_accessor = ctor_accessors.next().expect("ctor fields accessor");
        let nil_constructor = nil_variant.constructor;
        let cons_constructor = cons_variant.constructor;
        let mut cons_accessors = cons_variant.accessors.into_iter();
        let list_head = cons_accessors.next().expect("list head accessor");
        let list_tail = cons_accessors.next().expect("list tail accessor");

        let bool_encoding = Rc::new(PrimitiveEncoding {
            boxed: bool_boxed,
            unboxed: bool_unboxed,
            tag: bool_tag,
        });
        let int_encoding = Rc::new(PrimitiveEncoding {
            boxed: int_boxed,
            unboxed: int_unboxed,
            tag: int_tag,
        });

        let tag_function = RecFuncDecl::new("ctortag", &[&value_sort], &Sort::int());
        let tag_value = Dynamic::new_const("ctortag_value", &value_sort);
        let is_bool = bool_tester
            .apply(&[&tag_value])
            .as_bool()
            .expect("bool tester");
        let is_int = int_tester
            .apply(&[&tag_value])
            .as_bool()
            .expect("int tester");
        let ctor_tag = ctor_tag_accessor
            .apply(&[&tag_value])
            .as_int()
            .expect("ctor tag accessor");
        let tag_body = is_bool.ite(
            &bool_encoding.tag,
            &is_int.ite(&int_encoding.tag, &ctor_tag),
        );
        tag_function.add_def(&[&tag_value], &tag_body);

        Self {
            pointer_width_bits,
            value_sort,
            tag_function,
            generic_ctor: ctor_constructor,
            generic_ctor_fields: ctor_fields_accessor,
            list_nil: nil_constructor,
            list_cons: cons_constructor,
            list_head,
            list_tail,
            bool_encoding,
            int_encoding,
            next_ctor_tag: Cell::new(2),
            type_encodings: RefCell::new(BTreeMap::new()),
        }
    }

    pub(crate) fn value_sort(&self) -> &Sort {
        &self.value_sort
    }

    pub(crate) fn tag_function(&self) -> &FuncDecl {
        &self.tag_function
    }

    pub(crate) fn type_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<TypeEncoding>, String> {
        if let Some(encoding) = self.type_encodings.borrow().get(ty).cloned() {
            return Ok(encoding);
        }
        let encoding = self.build_type_encoding(ty, solver)?;
        self.type_encodings
            .borrow_mut()
            .insert(ty.clone(), encoding.clone());
        Ok(encoding)
    }

    pub(crate) fn inductive_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<InductiveEncoding>, String> {
        let encoding = self.type_encoding(ty, solver)?;
        match &encoding.kind {
            TypeEncodingKind::Inductive(encoding) => Ok(encoding.clone()),
            _ => Err(format!("expected inductive-backed spec type, found {ty:?}")),
        }
    }

    fn build_type_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<TypeEncoding>, String> {
        let encoding = match ty {
            SpecTy::Bool => TypeEncoding {
                sort: self.value_sort.clone(),
                kind: TypeEncodingKind::Bool(self.bool_encoding.clone()),
                semantics: TypeSemantics::Bool,
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
                sort: self.value_sort.clone(),
                kind: TypeEncodingKind::Int(self.int_encoding.clone()),
                semantics: TypeSemantics::Int {
                    bounds: self.int_bounds(ty)?,
                },
            },
            SpecTy::Tuple(_) | SpecTy::Struct(_) | SpecTy::Ref(_) | SpecTy::Mut(_) => {
                let inductive = self.build_inductive_encoding(ty, solver)?;
                TypeEncoding {
                    sort: self.value_sort.clone(),
                    kind: TypeEncodingKind::Inductive(inductive),
                    semantics: match ty {
                        SpecTy::Ref(_) => TypeSemantics::Ref,
                        SpecTy::Mut(_) => TypeSemantics::Mut,
                        SpecTy::Tuple(_) => TypeSemantics::Tuple,
                        SpecTy::Struct(_) => TypeSemantics::Struct,
                        _ => unreachable!("inductive encoding requires inductive spec type"),
                    },
                }
            }
        };
        Ok(Rc::new(encoding))
    }

    fn build_inductive_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<InductiveEncoding>, String> {
        let field_labels = self.inductive_field_names(ty)?;
        let field_encodings = self.inductive_field_encodings(ty, solver)?;
        let ctor_name = format!("mk_{}", self.sort_name(ty));
        let tag_value = Int::from_u64(u64::from(self.next_ctor_tag.get()));
        self.next_ctor_tag.set(self.next_ctor_tag.get() + 1);

        let domain_sorts = field_encodings
            .iter()
            .map(|field| &field.sort)
            .collect::<Vec<_>>();
        let constructor = RecFuncDecl::new(ctor_name.as_str(), &domain_sorts, &self.value_sort);
        let constructor_args = field_encodings
            .iter()
            .enumerate()
            .map(|(index, field)| {
                Dynamic::new_const(format!("{}_arg_{index}", ctor_name), &field.sort)
            })
            .collect::<Vec<_>>();
        let constructor_arg_refs = constructor_args
            .iter()
            .map(|arg| arg as &dyn Ast)
            .collect::<Vec<_>>();
        let constructor_list = self.value_list_from_values(&constructor_args);
        let constructor_body_args: Vec<&dyn Ast> = vec![&tag_value, &constructor_list];
        let constructor_body = self.generic_ctor.apply(&constructor_body_args);
        constructor.add_def(&constructor_arg_refs, &constructor_body);

        let accessors = field_labels
            .iter()
            .zip(field_encodings.iter())
            .enumerate()
            .map(|(index, (name, field))| {
                let accessor_name = format!("proj_{}_{}", self.sort_name(ty), name);
                let accessor = RecFuncDecl::new(accessor_name, &[&self.value_sort], &field.sort);
                let value =
                    Dynamic::new_const(format!("{}_value", self.sort_name(ty)), &self.value_sort);
                let fields = self.generic_ctor_fields.apply(&[&value]);
                let body = self.value_list_nth(&fields, index);
                accessor.add_def(&[&value], &body);
                accessor
            })
            .collect::<Vec<_>>();

        Ok(Rc::new(InductiveEncoding {
            constructor_name: ctor_name,
            field_labels,
            constructor,
            accessors,
            fields: field_encodings,
            tag: tag_value,
        }))
    }

    fn inductive_field_names(&self, ty: &SpecTy) -> Result<Vec<String>, String> {
        match ty {
            SpecTy::Ref(_) => Ok(vec!["deref".to_owned()]),
            SpecTy::Mut(_) => Ok(vec!["cur".to_owned(), "fin".to_owned()]),
            SpecTy::Tuple(items) => Ok((0..items.len()).map(|index| format!("_{index}")).collect()),
            SpecTy::Struct(StructTy { fields, .. }) => {
                Ok(fields.iter().map(|field| field.name.clone()).collect())
            }
            other => Err(format!(
                "expected inductive-backed spec type, found {other:?}"
            )),
        }
    }

    fn inductive_field_encodings(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Vec<Rc<TypeEncoding>>, String> {
        match ty {
            SpecTy::Ref(inner) => Ok(vec![self.type_encoding(inner, solver)?]),
            SpecTy::Mut(inner) => {
                let inner = self.type_encoding(inner, solver)?;
                Ok(vec![inner.clone(), inner])
            }
            SpecTy::Tuple(items) => items
                .iter()
                .map(|item| self.type_encoding(item, solver))
                .collect(),
            SpecTy::Struct(StructTy { fields, .. }) => fields
                .iter()
                .map(|field| self.type_encoding(&field.ty, solver))
                .collect(),
            other => Err(format!(
                "expected inductive-backed spec type, found {other:?}"
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

    fn int_bounds(&self, ty: &SpecTy) -> Result<Option<(Int, Int)>, String> {
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

    fn value_list_from_values(&self, values: &[Dynamic]) -> Dynamic {
        let mut list = self.list_nil.apply(&[]);
        for value in values.iter().rev() {
            list = self.list_cons.apply(&[value, &list]);
        }
        list
    }

    fn value_list_nth(&self, list: &Dynamic, index: usize) -> Dynamic {
        let mut current = list.clone();
        for _ in 0..index {
            current = self.list_tail.apply(&[&current]);
        }
        self.list_head.apply(&[&current])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::{StructFieldTy, StructTy};
    use z3::ast::{Ast, Bool};
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

        assert_eq!(bool_encoding.sort, *encoder.value_sort());
        assert_eq!(int_encoding.sort, *encoder.value_sort());
        assert_eq!(tuple_encoding.sort, *encoder.value_sort());
        assert_eq!(struct_encoding.sort, *encoder.value_sort());
        assert_eq!(bool_encoding.sort.kind(), SortKind::Datatype);
        assert_eq!(int_encoding.sort.kind(), SortKind::Datatype);
        assert_eq!(tuple_encoding.sort.kind(), SortKind::Datatype);
        assert_eq!(struct_encoding.sort.kind(), SortKind::Datatype);
    }

    #[test]
    fn assigns_projection_decls_and_tags() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let tuple_ty = SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]);
        let bool_encoding = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let int_encoding = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .inductive_encoding(&tuple_ty, &solver)
            .expect("tuple encoding");
        let TypeEncodingKind::Bool(bool_encoding) = &bool_encoding.kind else {
            panic!("bool encoding kind");
        };
        let TypeEncodingKind::Int(int_encoding) = &int_encoding.kind else {
            panic!("int encoding kind");
        };

        assert_eq!(tuple_encoding.accessors.len(), 2);
        assert_eq!(tuple_encoding.fields.len(), 2);
        assert_ne!(tuple_encoding.tag, bool_encoding.tag);
        assert_ne!(tuple_encoding.tag, int_encoding.tag);
    }

    #[test]
    fn records_constructor_accessors_and_tags() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let bool_encoding = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let int_encoding = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .inductive_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");

        let TypeEncodingKind::Bool(bool_primitive) = &bool_encoding.kind else {
            panic!("bool encoding kind");
        };
        let TypeEncodingKind::Int(int_primitive) = &int_encoding.kind else {
            panic!("int encoding kind");
        };

        assert_eq!(tuple_encoding.constructor_name, "mk_tuple_bool_i32");
        assert_eq!(tuple_encoding.accessors.len(), 2);
        assert_eq!(tuple_encoding.field_labels, vec!["_0", "_1"]);

        let tuple_value = tuple_encoding.constructor.apply(&[
            &bool_primitive.boxed.apply(&[&Bool::from_bool(true)]),
            &int_primitive.boxed.apply(&[&Int::from_i64(3)]),
        ]);
        assert_eq!(tuple_value.decl().name(), tuple_encoding.constructor_name);
        assert_eq!(tuple_value.children().len(), 2);
    }

    #[test]
    fn primitive_background_stays_sat_under_driver_solver_settings() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");

        let payload = Int::new_const("payload");
        solver.assert(&payload.ge(Int::from_i64(i64::from(i32::MIN))));
        solver.assert(&payload.le(Int::from_i64(i64::from(i32::MAX))));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn unit_constructor_background_stays_sat_under_driver_solver_settings() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        encoder
            .type_encoding(&SpecTy::Tuple(Vec::new()), &solver)
            .expect("unit encoding");

        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn unit_and_int_background_discharge_trivial_unsat_under_driver_settings() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        encoder
            .type_encoding(&SpecTy::Tuple(Vec::new()), &solver)
            .expect("unit encoding");
        encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");

        solver.assert(&Int::from_i64(1).eq(Int::from_i64(1)).not());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    #[test]
    fn tuple_constructor_background_stays_sat_under_driver_solver_settings() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        encoder
            .type_encoding(&SpecTy::Tuple(vec![SpecTy::I32, SpecTy::Bool]), &solver)
            .expect("tuple encoding");

        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn primitive_axioms_support_retract_tag_and_disjointness() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        let bool_encoding = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let int_encoding = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let TypeEncodingKind::Bool(bool_encoding) = &bool_encoding.kind else {
            panic!("bool encoding kind");
        };
        let TypeEncodingKind::Int(int_encoding) = &int_encoding.kind else {
            panic!("int encoding kind");
        };

        let payload = Bool::new_const("payload");
        let boxed_bool = bool_encoding.boxed.apply(&[&payload]);
        let unboxed_bool = bool_encoding
            .unboxed
            .apply(&[&boxed_bool])
            .as_bool()
            .expect("unboxed bool");

        solver.push();
        solver.assert(&unboxed_bool.eq(&payload).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        let bool_tag = encoder
            .tag_function()
            .apply(&[&boxed_bool])
            .as_int()
            .expect("bool tag");
        solver.push();
        solver.assert(&bool_tag.eq(&bool_encoding.tag).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        let int_payload = Int::new_const("int_payload");
        let boxed_int = int_encoding.boxed.apply(&[&int_payload]);
        solver.push();
        solver.assert(&boxed_bool.eq(&boxed_int));
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);
    }

    #[test]
    fn inductive_axioms_support_projection_and_tag_reasoning() {
        z3::set_global_param("smt.auto_config", "false");
        z3::set_global_param("smt.mbqi", "false");

        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1_000);
        solver.set_params(&params);

        let encoder = ValueEncoder::new(64);
        let bool_encoding = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let int_encoding = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .inductive_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");
        let TypeEncodingKind::Bool(bool_encoding) = &bool_encoding.kind else {
            panic!("bool encoding kind");
        };
        let TypeEncodingKind::Int(int_encoding) = &int_encoding.kind else {
            panic!("int encoding kind");
        };

        let flag = Bool::new_const("flag");
        let count = Int::new_const("count");
        let tuple = tuple_encoding.constructor.apply(&[
            &bool_encoding.boxed.apply(&[&flag]),
            &int_encoding.boxed.apply(&[&count]),
        ]);

        let projected_flag = tuple_encoding.accessors[0].apply(&[&tuple]);
        let projected_count = tuple_encoding.accessors[1].apply(&[&tuple]);

        solver.push();
        solver.assert(&projected_flag.eq(bool_encoding.boxed.apply(&[&flag])).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        solver.push();
        solver.assert(
            &projected_count
                .eq(int_encoding.boxed.apply(&[&count]))
                .not(),
        );
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        let tuple_tag = encoder
            .tag_function()
            .apply(&[&tuple])
            .as_int()
            .expect("tuple tag");
        solver.push();
        solver.assert(&tuple_tag.eq(&tuple_encoding.tag).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);
    }
}
