use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::rc::Rc;
use std::str::FromStr;

use crate::spec::{SpecTy, StructTy};
use z3::ast::{self, Ast, Bool, Dynamic, Int};
use z3::{FuncDecl, Pattern, Solver, Sort, Symbol};

/*
Value encoding overview

All spec values inhabit one uninterpreted Z3 sort:

  value

Primitive values use dedicated boxing/unboxing symbols:

  (boolbox) : Bool -> value
  (bool)    : value -> Bool
  (intbox)  : Int -> value
  (int)     : value -> Int

The backend asserts the following primitive retract axioms:

  forall b: Bool. (bool)((boolbox)(b)) = b
    pattern: ((boolbox)(b))

  forall i: Int. (int)((intbox)(i)) = i
    pattern: ((intbox)(i))

  forall v: value. (intbox)((int)(v)) = v
    pattern: ((int)(v))

Composite values follow the same shape as VeriFast's constructor symbols:

  each composite type gets a fresh subtype id s
  each constructor family gets a fresh constructor tag k

For a spec type whose sanitized name is `<name>`, the backend creates:

  mk_<name>              : value^n -> value
  ctortag<s>             : value -> Int
  ctorinv_<name>_<i>     : value -> value
  TAG_<name>             : Int literal unique to the constructor family

and asserts the following axioms:

  forall x0 .. xn-1. ctortag<s>(mk_<name>(x0, .., xn-1)) = TAG_<name>
    pattern: mk_<name>(x0, .., xn-1)

  forall x0 .. xn-1. ctorinv_<name>_<i>(mk_<name>(x0, .., xn-1)) = xi
    pattern: mk_<name>(x0, .., xn-1)

The engine builds type formulas over these symbols:

  Bool(v)     := true
  Int_T(v)    := bounds_T((int)(v))
  Ref_T(v)    := ctortag<s>(v) = TAG_ref_T /\ T(ctorinv_ref_T_0(v))
  Mut_T(v)    := ctortag<s>(v) = TAG_mut_T /\
                 T(ctorinv_mut_T_0(v)) /\ T(ctorinv_mut_T_1(v))
  Tuple/Struct values are analogous: tag equality plus recursive field formulas.

This keeps every surface spec value in the single `value` universe while still
using Z3's native Bool/Int theories for primitive payloads. The engine does not
pattern-match constructor applications on the Rust side; projections, tags, and
payload access always go through these solver symbols.
*/

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SymValue {
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
    Composite(Rc<CompositeEncoding>),
}

#[derive(Debug)]
pub(crate) struct PrimitiveEncoding {
    pub(crate) boxed: FuncDecl,
    pub(crate) unboxed: FuncDecl,
}

#[derive(Debug)]
pub(crate) struct CompositeEncoding {
    pub(crate) constructor_name: String,
    pub(crate) constructor: FuncDecl,
    pub(crate) accessors: Vec<FuncDecl>,
    pub(crate) fields: Vec<Rc<TypeEncoding>>,
    pub(crate) tag_function: FuncDecl,
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
    bool_encoding: Rc<PrimitiveEncoding>,
    int_encoding: Rc<PrimitiveEncoding>,
    primitive_axioms_asserted: Cell<bool>,
    next_subtype_id: Cell<u32>,
    next_ctor_tag: Cell<u32>,
    type_encodings: RefCell<BTreeMap<SpecTy, Rc<TypeEncoding>>>,
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
            type_encodings: RefCell::new(BTreeMap::new()),
        }
    }

    pub(crate) fn type_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<TypeEncoding>, String> {
        self.ensure_primitive_axioms(solver);
        if let Some(encoding) = self.type_encodings.borrow().get(ty).cloned() {
            return Ok(encoding);
        }
        let encoding = self.build_type_encoding(ty, solver)?;
        self.type_encodings
            .borrow_mut()
            .insert(ty.clone(), encoding.clone());
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
                let composite = self.build_composite_encoding(ty, solver)?;
                TypeEncoding {
                    sort: self.value_sort.clone(),
                    kind: TypeEncodingKind::Composite(composite),
                    semantics: match ty {
                        SpecTy::Ref(_) => TypeSemantics::Ref,
                        SpecTy::Mut(_) => TypeSemantics::Mut,
                        SpecTy::Tuple(_) => TypeSemantics::Tuple,
                        SpecTy::Struct(_) => TypeSemantics::Struct,
                        _ => unreachable!("composite encoding requires composite spec type"),
                    },
                }
            }
        };
        Ok(Rc::new(encoding))
    }

    fn build_composite_encoding(
        &self,
        ty: &SpecTy,
        solver: &Solver,
    ) -> Result<Rc<CompositeEncoding>, String> {
        let field_labels = self.composite_field_names(ty)?;
        let field_encodings = self.composite_field_encodings(ty, solver)?;
        let sort_name = self.sort_name(ty);
        let subtype_id = self.next_subtype_id.get();
        self.next_subtype_id.set(subtype_id + 1);
        let constructor_name = format!("mk_{sort_name}");
        let tag_function_name = format!("ctortag{subtype_id}");
        let tag = Int::from_u64(u64::from(self.next_ctor_tag.get()));
        self.next_ctor_tag.set(self.next_ctor_tag.get() + 1);

        let domain_sorts = field_encodings
            .iter()
            .map(|field| &field.sort)
            .collect::<Vec<_>>();
        let constructor = FuncDecl::new(constructor_name.as_str(), &domain_sorts, &self.value_sort);
        let accessors = field_labels
            .iter()
            .zip(field_encodings.iter())
            .map(|(label, field)| {
                FuncDecl::new(
                    format!("ctorinv_{sort_name}_{label}"),
                    &[&self.value_sort],
                    &field.sort,
                )
            })
            .collect::<Vec<_>>();
        let tag_function = FuncDecl::new(tag_function_name, &[&self.value_sort], &Sort::int());

        let encoding = Rc::new(CompositeEncoding {
            constructor_name,
            constructor,
            accessors,
            fields: field_encodings,
            tag_function,
            tag,
        });
        self.assert_composite_axioms(&encoding, solver);
        Ok(encoding)
    }

    fn ensure_primitive_axioms(&self, solver: &Solver) {
        if self.primitive_axioms_asserted.get() {
            return;
        }
        self.assert_bool_retract_axiom(solver);
        self.assert_int_retract_axiom(solver);
        self.primitive_axioms_asserted.set(true);
    }

    fn assert_bool_retract_axiom(&self, solver: &Solver) {
        let payload = Bool::new_const("value_encoding_bool_payload");
        let boxed = self.bool_encoding.boxed.apply(&[&payload]);
        let unboxed = self
            .bool_encoding
            .unboxed
            .apply(&[&boxed])
            .as_bool()
            .expect("bool payload");
        self.assert_patterned_forall(solver, &[&payload], &boxed, &unboxed.eq(&payload));
    }

    fn assert_int_retract_axiom(&self, solver: &Solver) {
        let payload = Int::new_const("value_encoding_int_payload");
        let boxed = self.int_encoding.boxed.apply(&[&payload]);
        let unboxed = self
            .int_encoding
            .unboxed
            .apply(&[&boxed])
            .as_int()
            .expect("int payload");
        self.assert_patterned_forall(solver, &[&payload], &boxed, &unboxed.eq(&payload));

        let value = Dynamic::new_const("value_encoding_int_value", &self.value_sort);
        let int_view = self.int_encoding.unboxed.apply(&[&value]);
        let int_pattern = Pattern::new(&[&int_view]);
        let body = self.int_encoding.boxed.apply(&[&int_view]).eq(&value);
        solver.assert(ast::forall_const(&[&value], &[&int_pattern], &body));
    }

    fn assert_composite_axioms(&self, encoding: &CompositeEncoding, solver: &Solver) {
        let args = encoding
            .fields
            .iter()
            .enumerate()
            .map(|(index, field)| {
                Dynamic::new_const(
                    format!("{}_arg_{index}", encoding.constructor_name),
                    &field.sort,
                )
            })
            .collect::<Vec<_>>();
        let arg_refs = args.iter().map(|arg| arg as &dyn Ast).collect::<Vec<_>>();
        let constructor_app = encoding.constructor.apply(&arg_refs);
        let tag_eq = encoding
            .tag_function
            .apply(&[&constructor_app])
            .as_int()
            .expect("composite tag")
            .eq(&encoding.tag);
        self.assert_patterned_forall(solver, &arg_refs, &constructor_app, &tag_eq);

        for (index, accessor) in encoding.accessors.iter().enumerate() {
            let body = accessor.apply(&[&constructor_app]).eq(&args[index]);
            self.assert_patterned_forall(solver, &arg_refs, &constructor_app, &body);
        }
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

    fn composite_field_names(&self, ty: &SpecTy) -> Result<Vec<String>, String> {
        match ty {
            SpecTy::Ref(_) => Ok(vec!["deref".to_owned()]),
            SpecTy::Mut(_) => Ok(vec!["cur".to_owned(), "fin".to_owned()]),
            SpecTy::Tuple(items) => Ok((0..items.len()).map(|index| format!("_{index}")).collect()),
            SpecTy::Struct(StructTy { fields, .. }) => {
                Ok(fields.iter().map(|field| field.name.clone()).collect())
            }
            other => Err(format!(
                "expected composite-backed spec type, found {other:?}"
            )),
        }
    }

    fn composite_field_encodings(
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
                "expected composite-backed spec type, found {other:?}"
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

        assert_eq!(bool_encoding.sort, encoder.value_sort);
        assert_eq!(int_encoding.sort, encoder.value_sort);
        assert_eq!(tuple_encoding.sort, encoder.value_sort);
        assert_eq!(struct_encoding.sort, encoder.value_sort);
        assert_eq!(bool_encoding.sort.kind(), SortKind::Uninterpreted);
        assert_eq!(int_encoding.sort.kind(), SortKind::Uninterpreted);
        assert_eq!(tuple_encoding.sort.kind(), SortKind::Uninterpreted);
        assert_eq!(struct_encoding.sort.kind(), SortKind::Uninterpreted);
    }

    #[test]
    fn composite_constructors_are_uninterpreted_function_symbols() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let bool_encoding = encoder
            .type_encoding(&SpecTy::Bool, &solver)
            .expect("bool encoding");
        let int_encoding = encoder
            .type_encoding(&SpecTy::I32, &solver)
            .expect("int encoding");
        let tuple_encoding = encoder
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");

        let TypeEncodingKind::Bool(bool_primitive) = &bool_encoding.kind else {
            panic!("bool encoding kind");
        };
        let TypeEncodingKind::Int(int_primitive) = &int_encoding.kind else {
            panic!("int encoding kind");
        };

        assert_eq!(tuple_encoding.constructor_name, "mk_tuple_bool_i32");
        assert_eq!(tuple_encoding.accessors.len(), 2);

        let tuple_value = tuple_encoding.constructor.apply(&[
            &bool_primitive.boxed.apply(&[&Bool::from_bool(true)]),
            &int_primitive.boxed.apply(&[&Int::from_i64(3)]),
        ]);
        assert_eq!(tuple_value.decl().name(), tuple_encoding.constructor_name);
        assert_eq!(tuple_value.children().len(), 2);
        assert_eq!(tuple_value.get_sort().kind(), SortKind::Uninterpreted);
    }

    #[test]
    fn primitive_axioms_support_retracts() {
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

        let bool_payload = Bool::new_const("bool_payload");
        let boxed_bool = bool_encoding.boxed.apply(&[&bool_payload]);
        let unboxed_bool = bool_encoding
            .unboxed
            .apply(&[&boxed_bool])
            .as_bool()
            .expect("unboxed bool");

        solver.push();
        solver.assert(unboxed_bool.eq(&bool_payload).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        let int_payload = Int::new_const("int_payload");
        let boxed_int = int_encoding.boxed.apply(&[&int_payload]);
        let unboxed_int = int_encoding
            .unboxed
            .apply(&[&boxed_int])
            .as_int()
            .expect("unboxed int");

        solver.push();
        solver.assert(unboxed_int.eq(&int_payload).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        let opaque_value = Dynamic::new_const("opaque_value", &encoder.value_sort);
        let reboxed_int = int_encoding
            .boxed
            .apply(&[&int_encoding.unboxed.apply(&[&opaque_value])]);
        solver.push();
        solver.assert(reboxed_int.eq(&opaque_value).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);
    }

    #[test]
    fn composite_axioms_support_projection_and_tag_reasoning() {
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
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
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
        solver.assert(projected_flag.eq(bool_encoding.boxed.apply(&[&flag])).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        solver.push();
        solver.assert(
            projected_count
                .eq(int_encoding.boxed.apply(&[&count]))
                .not(),
        );
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);

        let tuple_tag = tuple_encoding
            .tag_function
            .apply(&[&tuple])
            .as_int()
            .expect("tuple tag");
        solver.push();
        solver.assert(tuple_tag.eq(&tuple_encoding.tag).not());
        assert_eq!(solver.check(), SatResult::Unsat);
        solver.pop(1);
    }

    #[test]
    fn composite_symbols_follow_verifast_style_naming() {
        let solver = Solver::new();
        let encoder = ValueEncoder::new(64);
        let tuple_encoding = encoder
            .composite_encoding(&SpecTy::Tuple(vec![SpecTy::Bool, SpecTy::I32]), &solver)
            .expect("tuple encoding");

        let tag_name = tuple_encoding.tag_function.name();
        assert!(tag_name.starts_with("ctortag"));
        assert!(
            tag_name["ctortag".len()..]
                .chars()
                .all(|ch| ch.is_ascii_digit())
        );

        for inverse in &tuple_encoding.accessors {
            assert!(inverse.name().starts_with("ctorinv"));
        }
    }
}
