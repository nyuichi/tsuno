#![allow(dead_code)]

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::spec::{SpecTy, StructTy};
use z3::ast::{Bool, Dynamic, Int};
use z3::{FuncDecl, Solver, Sort};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SymValue {
    Bool(PrimitiveValue<Bool>),
    Int(PrimitiveValue<Int>),
    Inductive(InductiveValue),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PrimitiveValue<T> {
    pub(crate) ast: Dynamic,
    pub(crate) data: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InductiveValue {
    pub(crate) ast: Dynamic,
}

#[derive(Debug)]
pub(crate) struct TypeEncoding {
    pub(crate) sort: Sort,
    pub(crate) kind: TypeEncodingKind,
}

#[derive(Debug)]
pub(crate) enum TypeEncodingKind {
    Bool(Rc<PrimitiveEncoding>),
    Int(Rc<PrimitiveEncoding>),
    Inductive(Rc<InductiveEncoding>),
}

#[derive(Debug)]
pub(crate) struct PrimitiveEncoding {
    pub(crate) boxed_name: String,
    pub(crate) boxed: FuncDecl,
    pub(crate) unboxed: FuncDecl,
    pub(crate) tag: Int,
}

#[derive(Debug)]
pub(crate) struct InductiveEncoding {
    pub(crate) constructor_name: String,
    pub(crate) field_labels: Vec<String>,
    pub(crate) constructor: FuncDecl,
    pub(crate) accessors: Vec<FuncDecl>,
    pub(crate) fields: Vec<Rc<TypeEncoding>>,
    pub(crate) tag: Int,
}

pub(crate) struct ValueEncoder {
    value_sort: Sort,
    tag_function: FuncDecl,
    next_ctor_tag: Cell<u32>,
    bool_encoding: RefCell<Option<Rc<PrimitiveEncoding>>>,
    int_encoding: RefCell<Option<Rc<PrimitiveEncoding>>>,
    type_encodings: RefCell<BTreeMap<SpecTy, Rc<TypeEncoding>>>,
}

impl ValueEncoder {
    pub(crate) fn new() -> Self {
        let value_sort = Sort::uninterpreted("inductive".into());
        let tag_function = FuncDecl::new("ctortag", &[&value_sort], &Sort::int());
        Self {
            value_sort,
            tag_function,
            next_ctor_tag: Cell::new(0),
            bool_encoding: RefCell::new(None),
            int_encoding: RefCell::new(None),
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
                kind: TypeEncodingKind::Bool(self.shared_primitive_encoding(
                    &self.bool_encoding,
                    "bool",
                    &Sort::bool(),
                    solver,
                )),
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
                kind: TypeEncodingKind::Int(self.shared_primitive_encoding(
                    &self.int_encoding,
                    "int",
                    &Sort::int(),
                    solver,
                )),
            },
            SpecTy::Tuple(_) | SpecTy::Struct(_) | SpecTy::Ref(_) | SpecTy::Mut(_) => {
                let inductive = self.build_inductive_encoding(ty, solver)?;
                TypeEncoding {
                    sort: self.value_sort.clone(),
                    kind: TypeEncodingKind::Inductive(inductive),
                }
            }
        };
        Ok(Rc::new(encoding))
    }

    fn register_retract_encoding(
        &self,
        name: &str,
        sort: &Sort,
        _solver: &Solver,
    ) -> PrimitiveEncoding {
        let boxed_name = format!("({name}box)");
        let boxed = FuncDecl::new(boxed_name.as_str(), &[sort], &self.value_sort);
        let unboxed = FuncDecl::new(format!("({name})"), &[&self.value_sort], sort);
        let tag = Int::from_u64(u64::from(self.next_ctor_tag.get()));
        self.next_ctor_tag.set(self.next_ctor_tag.get() + 1);

        PrimitiveEncoding {
            boxed_name,
            boxed,
            unboxed,
            tag,
        }
    }

    fn shared_primitive_encoding(
        &self,
        slot: &RefCell<Option<Rc<PrimitiveEncoding>>>,
        name: &str,
        sort: &Sort,
        solver: &Solver,
    ) -> Rc<PrimitiveEncoding> {
        if let Some(encoding) = slot.borrow().clone() {
            return encoding;
        }
        let encoding = Rc::new(self.register_retract_encoding(name, sort, solver));
        slot.borrow_mut().replace(encoding.clone());
        encoding
    }

    fn build_inductive_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<InductiveEncoding>, String> {
        let field_labels = self.inductive_field_names(ty)?;
        let field_encodings = self.inductive_field_encodings(ty, solver)?;
        let ctor_name = format!("mk_{}", self.sort_name(ty));
        let domain_sorts: Vec<_> = field_encodings.iter().map(|field| &field.sort).collect();
        let constructor = FuncDecl::new(ctor_name.as_str(), &domain_sorts, &self.value_sort);
        let accessors = field_labels
            .iter()
            .zip(field_encodings.iter())
            .map(|(name, field)| {
                FuncDecl::new(
                    format!("proj_{}_{}", self.sort_name(ty), name),
                    &[&self.value_sort],
                    &field.sort,
                )
            })
            .collect::<Vec<_>>();
        let tag_value = Int::from_u64(u64::from(self.next_ctor_tag.get()));
        self.next_ctor_tag.set(self.next_ctor_tag.get() + 1);

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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::{StructFieldTy, StructTy};
    use z3::ast::Ast;
    use z3::{SatResult, SortKind};

    #[test]
    fn encodes_all_types_in_shared_value_sort() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new();

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
        assert_eq!(bool_encoding.sort.kind(), SortKind::Uninterpreted);
        assert_eq!(int_encoding.sort.kind(), SortKind::Uninterpreted);
        assert_eq!(tuple_encoding.sort.kind(), SortKind::Uninterpreted);
        assert_eq!(struct_encoding.sort.kind(), SortKind::Uninterpreted);
    }

    #[test]
    fn assigns_projection_decls_and_tags() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new();
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
        let encoder = ValueEncoder::new();
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

        let encoder = ValueEncoder::new();
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

        let encoder = ValueEncoder::new();
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

        let encoder = ValueEncoder::new();
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

        let encoder = ValueEncoder::new();
        encoder
            .type_encoding(&SpecTy::Tuple(vec![SpecTy::I32, SpecTy::Bool]), &solver)
            .expect("tuple encoding");

        assert_eq!(solver.check(), SatResult::Sat);
    }
}
