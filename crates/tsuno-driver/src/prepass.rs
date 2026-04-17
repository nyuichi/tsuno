use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::ops::ControlFlow;

use crate::directive::{
    CollectedFunctionDirectives, DirectiveAttach, DirectiveError, DirectiveKind,
    collect_function_directives,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{
    EnumDef, Expr, LemmaDef, PureFnDef, SpecTy, StructFieldTy, StructTy, TypedExpr, TypedExprKind,
    parse_ghost_block,
};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{HirId, Pat, PatKind};
use rustc_middle::mir::{BasicBlock, Body, Local, PlaceElem, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::def_id::LocalDefId;
use rustc_span::{DUMMY_SP, Span, Symbol};

#[derive(Debug, Clone, Default)]
pub struct HirBindingInfo {
    pub spans: HashMap<HirId, Span>,
    pub by_name: HashMap<Symbol, Vec<(HirId, Span)>>,
}

#[derive(Debug, Clone, Default)]
pub struct ResolvedExprEnv {
    pub locals: HashMap<String, Local>,
    pub spec_vars: HashSet<String>,
}

#[derive(Debug, Clone)]
pub struct LoopContract {
    pub header: BasicBlock,
    pub hir_loop_id: HirId,
    pub invariant_block: BasicBlock,
    pub invariant: TypedExpr,
    pub resolution: ResolvedExprEnv,
    pub invariant_span: String,
    pub body_blocks: BTreeSet<BasicBlock>,
    pub exit_blocks: BTreeSet<BasicBlock>,
    pub written_locals: BTreeSet<rustc_middle::mir::Local>,
}

#[derive(Debug, Clone)]
pub struct LoopContracts {
    pub by_header: HashMap<BasicBlock, LoopContract>,
    pub by_invariant_block: HashMap<BasicBlock, BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct AssertionContract {
    pub assertion: TypedExpr,
    pub resolution: ResolvedExprEnv,
    pub assertion_span: String,
}

#[derive(Debug, Clone)]
pub struct AssumptionContract {
    pub assumption: TypedExpr,
    pub resolution: ResolvedExprEnv,
}

#[derive(Debug, Clone)]
pub struct LemmaCallContract {
    pub lemma_name: String,
    pub args: Vec<TypedExpr>,
    pub resolution: ResolvedExprEnv,
    pub span_text: String,
}

#[derive(Debug, Clone)]
pub enum ControlPointDirective {
    Assert(AssertionContract),
    Assume(AssumptionContract),
    LemmaCall(LemmaCallContract),
}

#[derive(Debug, Clone)]
pub struct ControlPointDirectives {
    pub by_control_point: HashMap<(BasicBlock, usize), Vec<ControlPointDirective>>,
}

#[derive(Debug, Clone)]
pub struct TypedPureFnDef {
    pub name: String,
    pub params: Vec<ContractParam>,
    pub result_ty: SpecTy,
    pub body: TypedExpr,
}

#[derive(Debug, Clone)]
pub enum TypedGhostStmt {
    Assert(TypedExpr),
    Assume(TypedExpr),
    Call {
        lemma_name: String,
        args: Vec<TypedExpr>,
    },
}

#[derive(Debug, Clone)]
pub struct TypedLemmaDef {
    pub name: String,
    pub params: Vec<ContractParam>,
    pub req: TypedExpr,
    pub ens: TypedExpr,
    pub body: Vec<TypedGhostStmt>,
    pub spec_vars: Vec<SpecVarBinding>,
}

#[derive(Debug, Clone)]
pub struct ContractParam {
    pub name: String,
    pub ty: SpecTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecVarBinding {
    pub name: String,
    pub ty: SpecTy,
}

#[derive(Debug, Clone)]
pub struct FunctionContract {
    pub params: Vec<ContractParam>,
    pub req: TypedExpr,
    #[allow(dead_code)]
    pub req_span: String,
    pub ens: TypedExpr,
    pub ens_span: String,
    pub spec_vars: Vec<SpecVarBinding>,
    pub result: SpecTy,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum LoweredDirectiveTarget {
    FunctionEntry,
    FunctionExit,
    ControlPoint(BasicBlock, usize),
    Loop {
        header: BasicBlock,
        invariant_block: BasicBlock,
    },
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct LoweredDirective {
    pub span: Span,
    pub span_text: String,
    pub kind: DirectiveKind,
    pub target: LoweredDirectiveTarget,
    pub expr: Expr,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct DirectivePrepass {
    pub directives: Vec<LoweredDirective>,
    pub loop_contracts: LoopContracts,
    pub control_point_directives: ControlPointDirectives,
    pub function_contract: Option<FunctionContract>,
    pub spec_vars: Vec<SpecVarBinding>,
}

#[derive(Debug, Clone)]
pub struct GlobalGhostPrepass {
    pub enums: HashMap<String, EnumDef>,
    pub pure_fns: HashMap<String, PureFnDef>,
    pub lemmas: HashMap<String, LemmaDef>,
    pub typed_pure_fns: Vec<TypedPureFnDef>,
    pub typed_lemmas: Vec<TypedLemmaDef>,
}

#[derive(Debug, Clone)]
pub struct FunctionPrepass {
    pub def_id: LocalDefId,
    pub prepass: DirectivePrepass,
}

#[derive(Debug, Clone)]
pub struct ProgramPrepass {
    pub ghosts: GlobalGhostPrepass,
    pub functions: Vec<FunctionPrepass>,
    pub contracts: HashMap<LocalDefId, FunctionContract>,
}

impl LoopContracts {
    pub fn empty() -> Self {
        Self {
            by_header: HashMap::new(),
            by_invariant_block: HashMap::new(),
        }
    }

    pub fn contract_by_header(&self, header: BasicBlock) -> Option<&LoopContract> {
        self.by_header.get(&header)
    }

    pub fn header_for_invariant_block(&self, block: BasicBlock) -> Option<BasicBlock> {
        self.by_invariant_block.get(&block).copied()
    }
}

impl ControlPointDirectives {
    pub fn empty() -> Self {
        Self {
            by_control_point: HashMap::new(),
        }
    }

    pub fn directives_at(
        &self,
        block: BasicBlock,
        statement_index: usize,
    ) -> Option<&[ControlPointDirective]> {
        self.by_control_point
            .get(&(block, statement_index))
            .map(Vec::as_slice)
    }
}

pub fn compute_function_prepass<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
    ghosts: &GlobalGhostPrepass,
) -> Result<DirectivePrepass, VerificationResult> {
    compute_directives(tcx, def_id, item_span, body, ghosts).map_err(|error| VerificationResult {
        function: tcx.def_path_str(def_id.to_def_id()),
        status: VerificationStatus::Unsupported,
        span: error
            .display_span
            .unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(error.span)),
        message: error.message,
    })
}

pub fn compute_program_prepass<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<ProgramPrepass, Vec<VerificationResult>> {
    let ghosts = match compute_global_ghost_prepass(tcx) {
        Ok(ghosts) => ghosts,
        Err(error) => {
            return Err(vec![VerificationResult {
                function: "prepass".to_owned(),
                status: VerificationStatus::Unsupported,
                span: error
                    .display_span
                    .unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(error.span)),
                message: error.message,
            }]);
        }
    };
    let mut functions = Vec::new();
    let mut contracts = HashMap::new();
    let mut errors = Vec::new();

    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::Fn { .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        match compute_function_prepass(tcx, def_id, item.span, &body.borrow(), &ghosts) {
            Ok(prepass) => {
                let contract = prepass
                    .function_contract
                    .clone()
                    .expect("successful function prepass must yield contract");
                contracts.insert(def_id, contract);
                functions.push(FunctionPrepass { def_id, prepass });
            }
            Err(error) => errors.push(error),
        }
    }

    if errors.is_empty() {
        Ok(ProgramPrepass {
            ghosts,
            functions,
            contracts,
        })
    } else {
        Err(errors)
    }
}

pub fn compute_global_ghost_prepass<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<GlobalGhostPrepass, LoopPrepassError> {
    let mut sources = Vec::new();
    let mut seen_sources = HashSet::new();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let loc = tcx.sess.source_map().lookup_char_pos(item.span.lo());
        let key = loc.file.start_pos;
        if seen_sources.insert(key) {
            sources.push((
                item.span,
                loc.file
                    .src
                    .as_ref()
                    .map_or_else(String::new, |src| src.as_str().to_owned()),
            ));
        }
    }

    let mut enum_defs = Vec::new();
    let mut pure_fn_defs = Vec::new();
    let mut lemma_defs = Vec::new();
    for (span, source) in sources {
        collect_ghost_items_in_source(
            &source,
            span,
            &mut enum_defs,
            &mut pure_fn_defs,
            &mut lemma_defs,
        )?;
    }

    let anchor_span = tcx
        .hir_free_items()
        .next()
        .map(|item_id| tcx.hir_item(item_id).span)
        .unwrap_or(DUMMY_SP);

    let mut enums = HashMap::new();
    for enum_def in enum_defs {
        if enums
            .insert(enum_def.name.clone(), enum_def.clone())
            .is_some()
        {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: format!("duplicate enum name `{}`", enum_def.name),
            });
        }
    }
    validate_enum_defs(&enums, anchor_span)?;

    let mut pure_fns = HashMap::new();
    let mut pure_fn_order = Vec::with_capacity(pure_fn_defs.len());
    for def in pure_fn_defs {
        if pure_fns.insert(def.name.clone(), def.clone()).is_some() {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: "duplicate pure function name".to_owned(),
            });
        }
        pure_fn_order.push(def.name);
    }

    let mut lemmas = HashMap::new();
    let mut lemma_order = Vec::with_capacity(lemma_defs.len());
    for lemma in lemma_defs {
        if pure_fns.contains_key(&lemma.name)
            || lemmas.insert(lemma.name.clone(), lemma.clone()).is_some()
        {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: "duplicate lemma name".to_owned(),
            });
        }
        lemma_order.push(lemma.name);
    }

    let typed_pure_fn_map = type_pure_fns(&pure_fns, &enums, anchor_span)?;
    let typed_lemma_map = type_lemmas(&lemmas, &pure_fns, &enums, anchor_span)?;

    Ok(GlobalGhostPrepass {
        enums,
        pure_fns,
        lemmas,
        typed_pure_fns: order_pure_fns(&typed_pure_fn_map, &pure_fn_order),
        typed_lemmas: order_lemmas(&typed_lemma_map, &lemma_order),
    })
}

pub fn compute_hir_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    binding_info: &HirBindingInfo,
) -> HashMap<HirId, rustc_middle::mir::Local> {
    let mut locals = HashMap::new();
    for (local, decl) in body.local_decls.iter_enumerated() {
        let mut matched = None;
        for (hir_id, span) in &binding_info.spans {
            if spans_match(tcx, decl.source_info.span, *span) {
                matched = Some(*hir_id);
                break;
            }
        }
        if matched.is_none() {
            matched = decl.source_info.scope.lint_root(&body.source_scopes);
        }
        if let Some(hir_id) = matched {
            locals.entry(hir_id).or_insert(local);
        }
    }
    locals
}

pub struct LoopPrepassError {
    pub span: Span,
    pub display_span: Option<String>,
    pub message: String,
}

#[derive(Debug, Clone, Default)]
struct SpecScope {
    visible: HashSet<String>,
    bound: HashSet<String>,
    ordered: Vec<String>,
}

impl SpecScope {
    fn bind(
        &mut self,
        name: &str,
        span: Span,
        display_span: Option<String>,
        kind: &str,
    ) -> Result<(), LoopPrepassError> {
        if self.bound.contains(name) {
            return Err(LoopPrepassError {
                span,
                display_span,
                message: format!("duplicate spec binding `?{name}` in //@ {kind}"),
            });
        }
        self.bound.insert(name.to_owned());
        self.visible.insert(name.to_owned());
        self.ordered.push(name.to_owned());
        Ok(())
    }

    fn ordered_with(&self, other: &Self) -> Vec<String> {
        let mut names = self.ordered.clone();
        for name in &other.ordered {
            if !self.bound.contains(name) {
                names.push(name.clone());
            }
        }
        names
    }

    fn typed_ordered(
        &self,
        inferred: &mut SpecTypeInference,
    ) -> Result<Vec<SpecVarBinding>, String> {
        typed_spec_vars_for_names(&self.ordered, inferred)
    }

    fn typed_ordered_with(
        &self,
        other: &Self,
        inferred: &mut SpecTypeInference,
    ) -> Result<Vec<SpecVarBinding>, String> {
        let names = self.ordered_with(other);
        typed_spec_vars_for_names(&names, inferred)
    }
}

struct ExprResolutionContext<'a> {
    pure_fns: &'a HashMap<String, PureFnDef>,
    enum_defs: &'a HashMap<String, EnumDef>,
    binding_info: &'a HirBindingInfo,
    hir_locals: &'a HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    kind: DirectiveKind,
    spec_scope: &'a mut SpecScope,
}

#[derive(Debug, Clone)]
enum InferredExprTy {
    Known(SpecTy),
    SpecVar(String),
    Unknown,
}

#[derive(Debug, Clone, Default)]
struct SpecTypeInference {
    parent: HashMap<String, String>,
    concrete: HashMap<String, SpecTy>,
}

impl SpecTypeInference {
    fn ensure_var(&mut self, name: &str) {
        self.parent
            .entry(name.to_owned())
            .or_insert_with(|| name.to_owned());
    }

    fn find(&mut self, name: &str) -> String {
        self.ensure_var(name);
        let parent = self.parent.get(name).cloned().expect("spec var parent");
        if parent == name {
            return parent;
        }
        let root = self.find(&parent);
        self.parent.insert(name.to_owned(), root.clone());
        root
    }

    fn union(&mut self, lhs: &str, rhs: &str) -> Result<(), String> {
        let lhs_root = self.find(lhs);
        let rhs_root = self.find(rhs);
        if lhs_root == rhs_root {
            return Ok(());
        }
        let lhs_ty = self.concrete.get(&lhs_root).cloned();
        let rhs_ty = self.concrete.get(&rhs_root).cloned();
        self.parent.insert(rhs_root.clone(), lhs_root.clone());
        match (lhs_ty, rhs_ty) {
            (Some(lhs_ty), Some(rhs_ty)) => {
                self.concrete
                    .insert(lhs_root.clone(), unify_spec_tys(&lhs_ty, &rhs_ty)?);
            }
            (Some(lhs_ty), None) => {
                self.concrete.insert(lhs_root.clone(), lhs_ty);
            }
            (None, Some(rhs_ty)) => {
                self.concrete.insert(lhs_root.clone(), rhs_ty);
            }
            (None, None) => {}
        }
        Ok(())
    }

    fn constrain(&mut self, name: &str, ty: &SpecTy) -> Result<(), String> {
        let root = self.find(name);
        match self.concrete.get(&root).cloned() {
            Some(existing) => {
                let unified = unify_spec_tys(&existing, ty)?;
                self.concrete.insert(root, unified);
            }
            None => {
                self.concrete.insert(root, ty.clone());
            }
        }
        Ok(())
    }

    fn resolved_ty(&mut self, name: &str) -> Option<SpecTy> {
        let root = self.find(name);
        self.concrete.get(&root).cloned()
    }
}

fn unify_spec_tys(lhs: &SpecTy, rhs: &SpecTy) -> Result<SpecTy, String> {
    match (lhs, rhs) {
        (SpecTy::Bool, SpecTy::Bool) => Ok(SpecTy::Bool),
        (SpecTy::IntLiteral, SpecTy::IntLiteral) => Ok(SpecTy::IntLiteral),
        (SpecTy::IntLiteral, rhs) if is_concrete_integer_spec_ty(rhs) => Ok(rhs.clone()),
        (lhs, SpecTy::IntLiteral) if is_concrete_integer_spec_ty(lhs) => Ok(lhs.clone()),
        (lhs, rhs) if lhs == rhs => Ok(lhs.clone()),
        (SpecTy::Ref(lhs), SpecTy::Ref(rhs)) => {
            Ok(SpecTy::Ref(Box::new(unify_spec_tys(lhs, rhs)?)))
        }
        (SpecTy::Mut(lhs), SpecTy::Mut(rhs)) => {
            Ok(SpecTy::Mut(Box::new(unify_spec_tys(lhs, rhs)?)))
        }
        (SpecTy::Tuple(lhs), SpecTy::Tuple(rhs)) if lhs.len() == rhs.len() => {
            let mut items = Vec::with_capacity(lhs.len());
            for (lhs, rhs) in lhs.iter().zip(rhs.iter()) {
                items.push(unify_spec_tys(lhs, rhs)?);
            }
            Ok(SpecTy::Tuple(items))
        }
        (SpecTy::Struct(lhs), SpecTy::Struct(rhs))
            if lhs.name == rhs.name && lhs.fields.len() == rhs.fields.len() =>
        {
            let mut fields = Vec::with_capacity(lhs.fields.len());
            for (lhs, rhs) in lhs.fields.iter().zip(rhs.fields.iter()) {
                if lhs.name != rhs.name {
                    return Err(format!(
                        "type mismatch between `{}` and `{}`",
                        display_spec_field_ty(lhs),
                        display_spec_field_ty(rhs)
                    ));
                }
                fields.push(StructFieldTy {
                    name: lhs.name.clone(),
                    ty: unify_spec_tys(&lhs.ty, &rhs.ty)?,
                });
            }
            Ok(SpecTy::Struct(StructTy {
                name: lhs.name.clone(),
                fields,
            }))
        }
        (SpecTy::Named(lhs), SpecTy::Named(rhs)) if lhs == rhs => Ok(SpecTy::Named(lhs.clone())),
        _ => Err(format!(
            "type mismatch between `{}` and `{}`",
            display_spec_ty(lhs),
            display_spec_ty(rhs)
        )),
    }
}

fn display_spec_ty(ty: &SpecTy) -> String {
    match ty {
        SpecTy::Bool => "bool".to_owned(),
        SpecTy::IntLiteral => "{integer}".to_owned(),
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
        SpecTy::Ref(inner) => format!("Ref<{}>", display_spec_ty(inner)),
        SpecTy::Mut(inner) => format!("Mut<{}>", display_spec_ty(inner)),
        SpecTy::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(display_spec_ty)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        SpecTy::Struct(struct_ty) => struct_ty.name.clone(),
        SpecTy::Named(name) => name.clone(),
    }
}

fn display_spec_field_ty(field: &StructFieldTy) -> String {
    format!("{}.{}", field.name, display_spec_ty(&field.ty))
}

fn is_integer_spec_ty(ty: &SpecTy) -> bool {
    matches!(
        ty,
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
            | SpecTy::Usize
    )
}

fn is_concrete_integer_spec_ty(ty: &SpecTy) -> bool {
    is_integer_spec_ty(ty) && *ty != SpecTy::IntLiteral
}

fn is_fully_inferred_spec_ty(ty: &SpecTy) -> bool {
    match ty {
        SpecTy::IntLiteral => false,
        SpecTy::Tuple(items) => items.iter().all(is_fully_inferred_spec_ty),
        SpecTy::Struct(struct_ty) => struct_ty
            .fields
            .iter()
            .all(|field| is_fully_inferred_spec_ty(&field.ty)),
        SpecTy::Named(_) => true,
        SpecTy::Ref(inner) | SpecTy::Mut(inner) => is_fully_inferred_spec_ty(inner),
        _ => true,
    }
}

fn inferred_spec_var_ty(inferred: &mut SpecTypeInference, name: &str) -> Result<SpecTy, String> {
    let ty = inferred
        .resolved_ty(name)
        .ok_or_else(|| format!("could not infer a type for `?{name}`"))?;
    if !is_fully_inferred_spec_ty(&ty) {
        return Err(format!("could not infer a type for `?{name}`"));
    }
    Ok(ty)
}

fn typed_spec_vars_for_names(
    names: &[String],
    inferred: &mut SpecTypeInference,
) -> Result<Vec<SpecVarBinding>, String> {
    names
        .iter()
        .map(|name| {
            Ok(SpecVarBinding {
                name: name.clone(),
                ty: inferred_spec_var_ty(inferred, name)?,
            })
        })
        .collect()
}

fn constrain_expr_ty(
    inferred: &mut SpecTypeInference,
    ty: &InferredExprTy,
    expected: &SpecTy,
) -> Result<(), String> {
    match ty {
        InferredExprTy::Known(actual) => {
            let _ = unify_spec_tys(actual, expected)?;
            Ok(())
        }
        InferredExprTy::SpecVar(name) => inferred.constrain(name, expected),
        InferredExprTy::Unknown => Ok(()),
    }
}

fn unify_expr_tys(
    inferred: &mut SpecTypeInference,
    lhs: &InferredExprTy,
    rhs: &InferredExprTy,
) -> Result<(), String> {
    match (lhs, rhs) {
        (InferredExprTy::Known(lhs), InferredExprTy::Known(rhs)) => {
            let _ = unify_spec_tys(lhs, rhs)?;
            Ok(())
        }
        (InferredExprTy::SpecVar(lhs), InferredExprTy::SpecVar(rhs)) => inferred.union(lhs, rhs),
        (InferredExprTy::SpecVar(name), InferredExprTy::Known(ty))
        | (InferredExprTy::Known(ty), InferredExprTy::SpecVar(name)) => {
            inferred.constrain(name, ty)
        }
        _ => Ok(()),
    }
}

fn numeric_expr_result_ty(
    inferred: &mut SpecTypeInference,
    lhs: &InferredExprTy,
    rhs: &InferredExprTy,
) -> Result<InferredExprTy, String> {
    unify_expr_tys(inferred, lhs, rhs)?;
    Ok(match (lhs, rhs) {
        (InferredExprTy::Known(lhs), InferredExprTy::Known(rhs)) => {
            InferredExprTy::Known(unify_spec_tys(lhs, rhs)?)
        }
        (InferredExprTy::SpecVar(name), InferredExprTy::Known(ty))
        | (InferredExprTy::Known(ty), InferredExprTy::SpecVar(name)) => {
            inferred.constrain(name, ty)?;
            InferredExprTy::Known(ty.clone())
        }
        (InferredExprTy::SpecVar(lhs), InferredExprTy::SpecVar(_rhs)) => inferred
            .resolved_ty(lhs)
            .map(InferredExprTy::Known)
            .unwrap_or_else(|| InferredExprTy::SpecVar(lhs.clone())),
        _ => InferredExprTy::Unknown,
    })
}

pub fn spec_ty_for_rust_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<SpecTy, String> {
    match ty.kind() {
        TyKind::Bool => Ok(SpecTy::Bool),
        TyKind::Int(kind) => Ok(match kind {
            ty::IntTy::I8 => SpecTy::I8,
            ty::IntTy::I16 => SpecTy::I16,
            ty::IntTy::I32 => SpecTy::I32,
            ty::IntTy::I64 => SpecTy::I64,
            ty::IntTy::Isize => SpecTy::Isize,
            other => return Err(format!("unsupported integer type {other:?}")),
        }),
        TyKind::Uint(kind) => Ok(match kind {
            ty::UintTy::U8 => SpecTy::U8,
            ty::UintTy::U16 => SpecTy::U16,
            ty::UintTy::U32 => SpecTy::U32,
            ty::UintTy::U64 => SpecTy::U64,
            ty::UintTy::Usize => SpecTy::Usize,
            other => return Err(format!("unsupported integer type {other:?}")),
        }),
        TyKind::Ref(_, inner, mutability) => {
            let inner = spec_ty_for_rust_ty(tcx, *inner)?;
            if mutability.is_mut() {
                Ok(SpecTy::Mut(Box::new(inner)))
            } else {
                Ok(SpecTy::Ref(Box::new(inner)))
            }
        }
        TyKind::Tuple(fields) => {
            let mut items = Vec::with_capacity(fields.len());
            for field in fields.iter() {
                items.push(spec_ty_for_rust_ty(tcx, field)?);
            }
            Ok(SpecTy::Tuple(items))
        }
        TyKind::Adt(adt_def, args) => {
            if !adt_def.is_struct() {
                return Err(format!("unsupported type {ty:?}"));
            }
            if !args.is_empty() {
                return Err(format!("generic structs are unsupported: {ty:?}"));
            }
            let mut fields = Vec::new();
            let name = tcx.def_path_str(adt_def.did());
            for field in adt_def.non_enum_variant().fields.iter() {
                fields.push(StructFieldTy {
                    name: field.name.to_string(),
                    ty: spec_ty_for_rust_ty(tcx, field.ty(tcx, args))?,
                });
            }
            Ok(SpecTy::Struct(StructTy { name, fields }))
        }
        other => Err(format!("unsupported type {other:?}")),
    }
}

fn lookup_enum_ctor<'a>(
    enum_defs: &'a HashMap<String, EnumDef>,
    func: &str,
) -> Option<(&'a EnumDef, usize)> {
    let (enum_name, ctor_name) = func.split_once("::")?;
    let enum_def = enum_defs.get(enum_name)?;
    let (ctor_index, _) = enum_def.ctor(ctor_name)?;
    Some((enum_def, ctor_index))
}

fn validate_named_spec_ty(ty: &SpecTy, enum_defs: &HashMap<String, EnumDef>) -> Result<(), String> {
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
        | SpecTy::Usize => Ok(()),
        SpecTy::Tuple(items) => {
            for item in items {
                validate_named_spec_ty(item, enum_defs)?;
            }
            Ok(())
        }
        SpecTy::Struct(struct_ty) => {
            for field in &struct_ty.fields {
                validate_named_spec_ty(&field.ty, enum_defs)?;
            }
            Ok(())
        }
        SpecTy::Named(name) => enum_defs
            .contains_key(name)
            .then_some(())
            .ok_or_else(|| format!("unknown spec type `{name}`")),
        SpecTy::Ref(_) | SpecTy::Mut(_) => {
            Err("Ref<T> and Mut<T> are not supported in spec enum definitions".to_owned())
        }
    }
}

fn validate_enum_defs(
    enum_defs: &HashMap<String, EnumDef>,
    span: Span,
) -> Result<(), LoopPrepassError> {
    for enum_def in enum_defs.values() {
        let mut seen = HashSet::new();
        for ctor in &enum_def.ctors {
            if !seen.insert(ctor.name.clone()) {
                return Err(LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "enum `{}` defines duplicate constructor `{}`",
                        enum_def.name, ctor.name
                    ),
                });
            }
            for field_ty in &ctor.fields {
                validate_named_spec_ty(field_ty, enum_defs).map_err(|message| {
                    LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!(
                            "enum `{}` constructor `{}`: {message}",
                            enum_def.name, ctor.name
                        ),
                    }
                })?;
            }
        }
    }
    Ok(())
}

fn type_pure_call(
    func: &str,
    args: &[Expr],
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_arg: &mut impl FnMut(&Expr) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
        let ctor = &enum_def.ctors[ctor_index];
        if ctor.fields.len() != args.len() {
            return Err(format!(
                "constructor `{func}` expects {} arguments, found {}",
                ctor.fields.len(),
                args.len()
            ));
        }
        let mut typed_args = Vec::with_capacity(args.len());
        for (arg, field_ty) in args.iter().zip(&ctor.fields) {
            let typed_arg = type_arg(arg)?;
            let unified = unify_spec_tys(&typed_arg.ty, field_ty)?;
            if unified != *field_ty {
                return Err(format!(
                    "constructor `{func}` expects `{}`, found `{}`",
                    display_spec_ty(field_ty),
                    display_spec_ty(&typed_arg.ty)
                ));
            }
            typed_args.push(typed_arg);
        }
        return Ok(TypedExpr {
            ty: SpecTy::Named(enum_def.name.clone()),
            kind: TypedExprKind::CtorCall {
                enum_name: enum_def.name.clone(),
                ctor_name: ctor.name.clone(),
                ctor_index,
                args: typed_args,
            },
        });
    }
    let Some(def) = pure_fns.get(func) else {
        return Err(format!("unknown pure function `{func}`"));
    };
    if def.params.len() != args.len() {
        return Err(format!(
            "pure function `{func}` expects {} arguments, found {}",
            def.params.len(),
            args.len()
        ));
    }
    let mut typed_args = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&def.params) {
        let typed_arg = type_arg(arg)?;
        let unified = unify_spec_tys(&typed_arg.ty, &param.ty)?;
        if unified != param.ty {
            return Err(format!(
                "pure function `{func}` parameter `{}` expects `{}`, found `{}`",
                param.name,
                display_spec_ty(&param.ty),
                display_spec_ty(&typed_arg.ty)
            ));
        }
        typed_args.push(typed_arg);
    }
    Ok(TypedExpr {
        ty: def.result_ty.clone(),
        kind: TypedExprKind::PureCall {
            func: func.to_owned(),
            args: typed_args,
        },
    })
}

fn infer_contract_expr_types(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(lit) => Ok(InferredExprTy::Known(lit.spec_ty())),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                inferred.ensure_var(name);
                return Ok(InferredExprTy::SpecVar(name.clone()));
            }
            if let Some(ty) = params.get(name) {
                return Ok(InferredExprTy::Known(ty.clone()));
            }
            if allow_result && name == "result" {
                return Ok(InferredExprTy::Known(result_ty.clone()));
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::Bind(name) => {
            spec_scope
                .bind(
                    name,
                    Span::default(),
                    None,
                    if allow_result { "ens" } else { "req" },
                )
                .map_err(|err| err.message)?;
            inferred.ensure_var(name);
            Ok(InferredExprTy::SpecVar(name.clone()))
        }
        Expr::Call { func, args } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                let ctor = &enum_def.ctors[ctor_index];
                if ctor.fields.len() != args.len() {
                    return Err(format!(
                        "constructor `{func}` expects {} arguments, found {}",
                        ctor.fields.len(),
                        args.len()
                    ));
                }
                for (arg, field_ty) in args.iter().zip(&ctor.fields) {
                    let arg_ty = infer_contract_expr_types(
                        arg,
                        pure_fns,
                        enum_defs,
                        spec_scope,
                        params,
                        allow_result,
                        result_ty,
                        inferred,
                    )?;
                    constrain_expr_ty(inferred, &arg_ty, field_ty)?;
                }
                Ok(InferredExprTy::Known(SpecTy::Named(enum_def.name.clone())))
            } else {
                let Some(def) = pure_fns.get(func) else {
                    return Err(format!("unknown pure function `{func}`"));
                };
                if def.params.len() != args.len() {
                    return Err(format!(
                        "pure function `{func}` expects {} arguments, found {}",
                        def.params.len(),
                        args.len()
                    ));
                }
                for (arg, param) in args.iter().zip(&def.params) {
                    let arg_ty = infer_contract_expr_types(
                        arg,
                        pure_fns,
                        enum_defs,
                        spec_scope,
                        params,
                        allow_result,
                        result_ty,
                        inferred,
                    )?;
                    constrain_expr_ty(inferred, &arg_ty, &param.ty)?;
                }
                Ok(InferredExprTy::Known(def.result_ty.clone()))
            }
        }
        Expr::Field { base, name } => {
            let base_ty = infer_contract_expr_types(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            infer_named_field_expr_type(base_ty, name)
        }
        Expr::TupleField { base, .. } => {
            let base_ty = infer_contract_expr_types(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            infer_tuple_field_expr_type(base_ty)
        }
        Expr::Deref { base } => {
            let base_ty = infer_contract_expr_types(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match base_ty {
                InferredExprTy::Known(SpecTy::Ref(inner))
                | InferredExprTy::Known(SpecTy::Mut(inner)) => Ok(InferredExprTy::Known(*inner)),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
                InferredExprTy::Known(other) => Err(format!(
                    "dereference requires Ref<T> or Mut<T>, found `{}`",
                    display_spec_ty(&other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg_ty = infer_contract_expr_types(
                arg,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match op {
                crate::spec::UnaryOp::Not => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::Bool)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::UnaryOp::Neg => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::IntLiteral)?;
                    Ok(arg_ty)
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs_ty = infer_contract_expr_types(
                lhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            let rhs_ty = infer_contract_expr_types(
                rhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match op {
                crate::spec::BinaryOp::Eq | crate::spec::BinaryOp::Ne => {
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::And | crate::spec::BinaryOp::Or => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Bool)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Bool)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::Lt
                | crate::spec::BinaryOp::Le
                | crate::spec::BinaryOp::Gt
                | crate::spec::BinaryOp::Ge => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                    let _ = numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::Add
                | crate::spec::BinaryOp::Sub
                | crate::spec::BinaryOp::Mul => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                    numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)
                }
            }
        }
    }
}

fn infer_body_expr_types(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(lit) => Ok(InferredExprTy::Known(lit.spec_ty())),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                inferred.ensure_var(name);
                return Ok(InferredExprTy::SpecVar(name.clone()));
            }
            local_tys
                .get(name)
                .cloned()
                .map(InferredExprTy::Known)
                .ok_or_else(|| format!("unresolved binding `{name}` in //@ {}", kind.keyword()))
        }
        Expr::Bind(name) => {
            spec_scope
                .bind(name, Span::default(), None, kind.keyword())
                .map_err(|err| err.message)?;
            inferred.ensure_var(name);
            Ok(InferredExprTy::SpecVar(name.clone()))
        }
        Expr::Call { func, args } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                let ctor = &enum_def.ctors[ctor_index];
                if ctor.fields.len() != args.len() {
                    return Err(format!(
                        "constructor `{func}` expects {} arguments, found {}",
                        ctor.fields.len(),
                        args.len()
                    ));
                }
                for (arg, field_ty) in args.iter().zip(&ctor.fields) {
                    let arg_ty = infer_body_expr_types(
                        arg, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
                    )?;
                    constrain_expr_ty(inferred, &arg_ty, field_ty)?;
                }
                Ok(InferredExprTy::Known(SpecTy::Named(enum_def.name.clone())))
            } else {
                let Some(def) = pure_fns.get(func) else {
                    return Err(format!("unknown pure function `{func}`"));
                };
                if def.params.len() != args.len() {
                    return Err(format!(
                        "pure function `{func}` expects {} arguments, found {}",
                        def.params.len(),
                        args.len()
                    ));
                }
                for (arg, param) in args.iter().zip(&def.params) {
                    let arg_ty = infer_body_expr_types(
                        arg, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
                    )?;
                    constrain_expr_ty(inferred, &arg_ty, &param.ty)?;
                }
                Ok(InferredExprTy::Known(def.result_ty.clone()))
            }
        }
        Expr::Field { base, name } => {
            let base_ty = infer_body_expr_types(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
            )?;
            infer_named_field_expr_type(base_ty, name)
        }
        Expr::TupleField { base, .. } => {
            let base_ty = infer_body_expr_types(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
            )?;
            infer_tuple_field_expr_type(base_ty)
        }
        Expr::Deref { base } => {
            let base_ty = infer_body_expr_types(
                base, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            match base_ty {
                InferredExprTy::Known(SpecTy::Ref(inner))
                | InferredExprTy::Known(SpecTy::Mut(inner)) => Ok(InferredExprTy::Known(*inner)),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
                InferredExprTy::Known(other) => Err(format!(
                    "dereference requires Ref<T> or Mut<T>, found `{}`",
                    display_spec_ty(&other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg_ty = infer_body_expr_types(
                arg, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            match op {
                crate::spec::UnaryOp::Not => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::Bool)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::UnaryOp::Neg => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::IntLiteral)?;
                    Ok(arg_ty)
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs_ty = infer_body_expr_types(
                lhs, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            let rhs_ty = infer_body_expr_types(
                rhs, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            match op {
                crate::spec::BinaryOp::Eq | crate::spec::BinaryOp::Ne => {
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::And | crate::spec::BinaryOp::Or => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Bool)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Bool)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::Lt
                | crate::spec::BinaryOp::Le
                | crate::spec::BinaryOp::Gt
                | crate::spec::BinaryOp::Ge => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                    let _ = numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::Add
                | crate::spec::BinaryOp::Sub
                | crate::spec::BinaryOp::Mul => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                    numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)
                }
            }
        }
    }
}

fn expr_base(base: &Expr) -> &Expr {
    base
}

fn infer_named_field_expr_type(
    base_ty: InferredExprTy,
    name: &str,
) -> Result<InferredExprTy, String> {
    match base_ty {
        InferredExprTy::Known(SpecTy::Struct(struct_ty)) => Ok(struct_ty
            .field(name)
            .map(|(_, field)| InferredExprTy::Known(field.ty.clone()))
            .unwrap_or(InferredExprTy::Unknown)),
        InferredExprTy::Known(SpecTy::Mut(inner)) if name == "fin" => {
            Ok(InferredExprTy::Known(*inner))
        }
        InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
        InferredExprTy::Known(other) => Err(format!(
            "field access requires a struct or Mut<T>. found `{}`",
            display_spec_ty(&other)
        )),
    }
}

fn infer_tuple_field_expr_type(base_ty: InferredExprTy) -> Result<InferredExprTy, String> {
    match base_ty {
        InferredExprTy::Known(SpecTy::Tuple(_)) => Ok(InferredExprTy::Unknown),
        InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
        InferredExprTy::Known(SpecTy::Struct(_)) => {
            Err("tuple field access is not supported on struct types".to_owned())
        }
        InferredExprTy::Known(other) => Err(format!(
            "tuple field access requires a tuple, found `{}`",
            display_spec_ty(&other)
        )),
    }
}

fn local_spec_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    resolved: &ResolvedExprEnv,
) -> Result<HashMap<String, SpecTy>, String> {
    let mut types = HashMap::new();
    for (name, local) in &resolved.locals {
        let ty = spec_ty_for_rust_ty(tcx, body.local_decls[*local].ty)?;
        types.insert(name.clone(), ty);
    }
    Ok(types)
}

fn typed_contract_expr(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<TypedExpr, String> {
    match expr {
        Expr::Bool(value) => Ok(TypedExpr {
            ty: SpecTy::Bool,
            kind: TypedExprKind::Bool(*value),
        }),
        Expr::Int(lit) => Ok(TypedExpr {
            ty: lit.spec_ty(),
            kind: TypedExprKind::Int(lit.clone()),
        }),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                let ty = inferred_spec_var_ty(inferred, name)?;
                return Ok(TypedExpr {
                    ty,
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            if let Some(ty) = params.get(name) {
                return Ok(TypedExpr {
                    ty: ty.clone(),
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            if allow_result && name == "result" {
                return Ok(TypedExpr {
                    ty: result_ty.clone(),
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::Bind(name) => {
            spec_scope
                .bind(
                    name,
                    Span::default(),
                    None,
                    if allow_result { "ens" } else { "req" },
                )
                .map_err(|err| err.message)?;
            let ty = inferred_spec_var_ty(inferred, name)?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::Bind(name.clone()),
            })
        }
        Expr::Call { func, args } => type_pure_call(func, args, pure_fns, enum_defs, &mut |arg| {
            typed_contract_expr(
                arg,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )
        }),
        Expr::Field { base, name } => {
            let base = typed_contract_expr(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            type_named_field_expr(base, name)
        }
        Expr::TupleField { base, index } => {
            let base = typed_contract_expr(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            type_tuple_field_expr(base, *index)
        }
        Expr::Deref { base } => {
            let base = typed_contract_expr(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match &base.ty {
                SpecTy::Ref(inner) | SpecTy::Mut(inner) => Ok(TypedExpr {
                    ty: (**inner).clone(),
                    kind: TypedExprKind::Deref {
                        base: Box::new(base),
                    },
                }),
                other => Err(format!(
                    "dereference requires Ref<T> or Mut<T>, found `{}`",
                    display_spec_ty(other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg = typed_contract_expr(
                arg,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match op {
                crate::spec::UnaryOp::Not => {
                    if arg.ty != SpecTy::Bool {
                        return Err(format!(
                            "`!` requires `bool`, found `{}`",
                            display_spec_ty(&arg.ty)
                        ));
                    }
                    Ok(TypedExpr {
                        ty: SpecTy::Bool,
                        kind: TypedExprKind::Unary {
                            op: *op,
                            arg: Box::new(arg),
                        },
                    })
                }
                crate::spec::UnaryOp::Neg => {
                    if !is_integer_spec_ty(&arg.ty) {
                        return Err(format!(
                            "unary `-` requires an integer, found `{}`",
                            display_spec_ty(&arg.ty)
                        ));
                    }
                    Ok(TypedExpr {
                        ty: arg.ty.clone(),
                        kind: TypedExprKind::Unary {
                            op: *op,
                            arg: Box::new(arg),
                        },
                    })
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs = typed_contract_expr(
                lhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            let rhs = typed_contract_expr(
                rhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            type_binary_expr(*op, lhs, rhs)
        }
    }
}

fn typed_body_expr(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<TypedExpr, String> {
    match expr {
        Expr::Bool(value) => Ok(TypedExpr {
            ty: SpecTy::Bool,
            kind: TypedExprKind::Bool(*value),
        }),
        Expr::Int(lit) => Ok(TypedExpr {
            ty: lit.spec_ty(),
            kind: TypedExprKind::Int(lit.clone()),
        }),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                let ty = inferred_spec_var_ty(inferred, name)?;
                return Ok(TypedExpr {
                    ty,
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            let ty = local_tys
                .get(name)
                .cloned()
                .ok_or_else(|| format!("unresolved binding `{name}` in //@ {}", kind.keyword()))?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::Var(name.clone()),
            })
        }
        Expr::Bind(name) => {
            spec_scope
                .bind(name, Span::default(), None, kind.keyword())
                .map_err(|err| err.message)?;
            let ty = inferred_spec_var_ty(inferred, name)?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::Bind(name.clone()),
            })
        }
        Expr::Call { func, args } => type_pure_call(func, args, pure_fns, enum_defs, &mut |arg| {
            typed_body_expr(
                arg, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )
        }),
        Expr::Field { base, name } => {
            let base = typed_body_expr(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
            )?;
            type_named_field_expr(base, name)
        }
        Expr::TupleField { base, index } => {
            let base = typed_body_expr(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
            )?;
            type_tuple_field_expr(base, *index)
        }
        Expr::Deref { base } => {
            let base = typed_body_expr(
                base, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            match &base.ty {
                SpecTy::Ref(inner) | SpecTy::Mut(inner) => Ok(TypedExpr {
                    ty: (**inner).clone(),
                    kind: TypedExprKind::Deref {
                        base: Box::new(base),
                    },
                }),
                other => Err(format!(
                    "dereference requires Ref<T> or Mut<T>, found `{}`",
                    display_spec_ty(other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg = typed_body_expr(
                arg, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            match op {
                crate::spec::UnaryOp::Not => {
                    if arg.ty != SpecTy::Bool {
                        return Err(format!(
                            "`!` requires `bool`, found `{}`",
                            display_spec_ty(&arg.ty)
                        ));
                    }
                    Ok(TypedExpr {
                        ty: SpecTy::Bool,
                        kind: TypedExprKind::Unary {
                            op: *op,
                            arg: Box::new(arg),
                        },
                    })
                }
                crate::spec::UnaryOp::Neg => {
                    if !is_integer_spec_ty(&arg.ty) {
                        return Err(format!(
                            "unary `-` requires an integer, found `{}`",
                            display_spec_ty(&arg.ty)
                        ));
                    }
                    Ok(TypedExpr {
                        ty: arg.ty.clone(),
                        kind: TypedExprKind::Unary {
                            op: *op,
                            arg: Box::new(arg),
                        },
                    })
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs = typed_body_expr(
                lhs, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            let rhs = typed_body_expr(
                rhs, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred,
            )?;
            type_binary_expr(*op, lhs, rhs)
        }
    }
}

fn type_binary_expr(
    op: crate::spec::BinaryOp,
    lhs: TypedExpr,
    rhs: TypedExpr,
) -> Result<TypedExpr, String> {
    match op {
        crate::spec::BinaryOp::Eq | crate::spec::BinaryOp::Ne => {
            let _ = unify_spec_tys(&lhs.ty, &rhs.ty)?;
            if matches!(lhs.ty, SpecTy::Ref(_) | SpecTy::Mut(_)) {
                return Err(format!(
                    "`==` and `!=` are not supported for `{}`",
                    display_spec_ty(&lhs.ty)
                ));
            }
            Ok(TypedExpr {
                ty: SpecTy::Bool,
                kind: TypedExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            })
        }
        crate::spec::BinaryOp::And | crate::spec::BinaryOp::Or => {
            if lhs.ty != SpecTy::Bool || rhs.ty != SpecTy::Bool {
                return Err(format!(
                    "logical operators require `bool`, found `{}` and `{}`",
                    display_spec_ty(&lhs.ty),
                    display_spec_ty(&rhs.ty)
                ));
            }
            Ok(TypedExpr {
                ty: SpecTy::Bool,
                kind: TypedExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            })
        }
        crate::spec::BinaryOp::Lt
        | crate::spec::BinaryOp::Le
        | crate::spec::BinaryOp::Gt
        | crate::spec::BinaryOp::Ge => {
            let unified = unify_spec_tys(&lhs.ty, &rhs.ty)?;
            if !is_integer_spec_ty(&unified) {
                return Err(format!(
                    "comparison requires integers, found `{}` and `{}`",
                    display_spec_ty(&lhs.ty),
                    display_spec_ty(&rhs.ty)
                ));
            }
            Ok(TypedExpr {
                ty: SpecTy::Bool,
                kind: TypedExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            })
        }
        crate::spec::BinaryOp::Add | crate::spec::BinaryOp::Sub | crate::spec::BinaryOp::Mul => {
            let unified = unify_spec_tys(&lhs.ty, &rhs.ty)?;
            if !is_integer_spec_ty(&unified) {
                return Err(format!(
                    "arithmetic requires integers, found `{}` and `{}`",
                    display_spec_ty(&lhs.ty),
                    display_spec_ty(&rhs.ty)
                ));
            }
            Ok(TypedExpr {
                ty: unified,
                kind: TypedExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            })
        }
    }
}

fn type_named_field_expr(base: TypedExpr, name: &str) -> Result<TypedExpr, String> {
    if name == "fin"
        && let SpecTy::Mut(inner) = &base.ty
    {
        return Ok(TypedExpr {
            ty: (**inner).clone(),
            kind: TypedExprKind::Fin {
                base: Box::new(base),
            },
        });
    }
    let SpecTy::Struct(struct_ty) = &base.ty else {
        return Err(format!(
            "field access requires a struct, found `{}`",
            display_spec_ty(&base.ty)
        ));
    };
    let Some((index, field_ty)) = struct_ty.field(name) else {
        return Err(format!(
            "struct `{}` does not have a field named `{name}`",
            struct_ty.name
        ));
    };
    Ok(TypedExpr {
        ty: field_ty.ty.clone(),
        kind: TypedExprKind::Field {
            base: Box::new(base),
            name: name.to_owned(),
            index,
        },
    })
}

fn type_tuple_field_expr(base: TypedExpr, index: usize) -> Result<TypedExpr, String> {
    let SpecTy::Tuple(items) = &base.ty else {
        if matches!(base.ty, SpecTy::Struct(_)) {
            return Err("tuple field access is not supported on struct types".to_owned());
        }
        return Err(format!(
            "tuple field access requires a tuple, found `{}`",
            display_spec_ty(&base.ty)
        ));
    };
    let Some(field_ty) = items.get(index) else {
        return Err(format!("tuple field .{index} is out of bounds"));
    };
    Ok(TypedExpr {
        ty: field_ty.clone(),
        kind: TypedExprKind::TupleField {
            base: Box::new(base),
            index,
        },
    })
}

pub fn compute_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
    ghosts: &GlobalGhostPrepass,
) -> Result<DirectivePrepass, LoopPrepassError> {
    let enum_defs = &ghosts.enums;
    let pure_fns = &ghosts.pure_fns;
    let lemma_defs = &ghosts.lemmas;
    let binding_info = collect_hir_binding_info(tcx, def_id)?;
    let hir_locals = compute_hir_locals(tcx, body, &binding_info);
    let directives =
        collect_function_directives(tcx, def_id, item_span).map_err(directive_error_to_prepass)?;
    let mut contract_scope = SpecScope::default();
    let mut req_directive = None;
    let mut ens_directive = None;
    for directive in &directives.directives {
        match directive.kind {
            DirectiveKind::Req => {
                if req_directive.replace(directive).is_some() {
                    return Err(LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message: "multiple //@ req directives for a function".to_owned(),
                    });
                }
            }
            DirectiveKind::Ens => {
                if ens_directive.replace(directive).is_some() {
                    return Err(LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message: "multiple //@ ens directives for a function".to_owned(),
                    });
                }
            }
            _ => {}
        }
    }
    let param_names = if req_directive.is_some() || ens_directive.is_some() {
        function_param_names(tcx, def_id).map_err(|err| LoopPrepassError {
            span: tcx.def_span(def_id.to_def_id()),
            display_span: None,
            message: err.message,
        })?
    } else {
        function_param_names_relaxed(tcx, def_id)
    };
    let (params, result) = function_contract_signature_with_names(tcx, def_id, param_names.clone())
        .map_err(|err| LoopPrepassError {
            span: tcx.def_span(def_id.to_def_id()),
            display_span: None,
            message: err.message,
        })?;
    let param_tys: HashMap<_, _> = params
        .iter()
        .map(|param| (param.name.clone(), param.ty.clone()))
        .collect();
    let result_ty = result.clone();
    if let Some(directive) = req_directive {
        validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            &directive.expr,
            pure_fns,
            enum_defs,
            &param_names,
            false,
            &mut contract_scope,
        )?
    }
    let mut body_scope = contract_scope.clone();
    let mut resolved_exprs = HashMap::new();
    for directive in directives.directives.iter().filter(|directive| {
        matches!(
            directive.kind,
            DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::Inv
                | DirectiveKind::LemmaCall
        )
    }) {
        let resolution = match directive.kind {
            DirectiveKind::LemmaCall => resolve_lemma_call_expr_env(
                &directive.expr,
                pure_fns,
                enum_defs,
                &binding_info,
                &hir_locals,
                directive.span,
                directive_anchor_span(&directive.attach),
                lemma_defs,
                &mut body_scope,
            )?,
            _ => resolve_expr_env(
                &directive.expr,
                pure_fns,
                enum_defs,
                &binding_info,
                &hir_locals,
                directive.span,
                directive_anchor_span(&directive.attach),
                directive.kind,
                &mut body_scope,
            )?,
        };
        resolved_exprs.insert(directive.span_text.clone(), resolution);
    }
    if let Some(directive) = ens_directive {
        validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            &directive.expr,
            pure_fns,
            enum_defs,
            &param_names,
            true,
            &mut contract_scope,
        )?
    }
    let mut inferred = SpecTypeInference::default();
    let mut contract_infer_scope = SpecScope::default();
    if let Some(directive) = req_directive {
        infer_contract_expr_types(
            &directive.expr,
            pure_fns,
            enum_defs,
            &mut contract_infer_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span: directive.span,
            display_span: Some(directive.span_text.clone()),
            message,
        })?;
    }
    let mut body_infer_scope = contract_infer_scope.clone();
    let mut typed_lemma_calls = HashMap::new();
    for directive in directives.directives.iter().filter(|directive| {
        matches!(
            directive.kind,
            DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::Inv
                | DirectiveKind::LemmaCall
        )
    }) {
        let resolution = resolved_exprs
            .get(&directive.span_text)
            .expect("resolved body expression");
        let local_tys =
            local_spec_tys(tcx, body, resolution).map_err(|message| LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message,
            })?;
        match directive.kind {
            DirectiveKind::LemmaCall => {
                infer_lemma_call(
                    &directive.expr,
                    lemma_defs,
                    pure_fns,
                    enum_defs,
                    &mut body_infer_scope,
                    &local_tys,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?;
            }
            _ => {
                infer_body_expr_types(
                    &directive.expr,
                    pure_fns,
                    enum_defs,
                    directive.kind,
                    &mut body_infer_scope,
                    &local_tys,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?;
            }
        }
    }
    if let Some(directive) = ens_directive {
        infer_contract_expr_types(
            &directive.expr,
            pure_fns,
            enum_defs,
            &mut contract_infer_scope,
            &param_tys,
            true,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span: directive.span,
            display_span: Some(directive.span_text.clone()),
            message,
        })?;
    }
    let def_span = tcx
        .sess
        .source_map()
        .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id()));
    let typed_req = match req_directive {
        Some(directive) => {
            let mut scope = SpecScope::default();
            Some(
                typed_contract_expr(
                    &directive.expr,
                    pure_fns,
                    enum_defs,
                    &mut scope,
                    &param_tys,
                    false,
                    &result_ty,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?,
            )
        }
        None => None,
    };
    let mut typed_body_exprs = HashMap::new();
    let mut body_type_scope = if req_directive.is_some() {
        let mut scope = SpecScope::default();
        if let Some(directive) = req_directive {
            let _ = typed_contract_expr(
                &directive.expr,
                pure_fns,
                enum_defs,
                &mut scope,
                &param_tys,
                false,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message,
            })?;
        }
        scope
    } else {
        SpecScope::default()
    };
    for directive in directives.directives.iter().filter(|directive| {
        matches!(
            directive.kind,
            DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::Inv
                | DirectiveKind::LemmaCall
        )
    }) {
        let resolution = resolved_exprs
            .get(&directive.span_text)
            .expect("resolved body expression");
        let local_tys =
            local_spec_tys(tcx, body, resolution).map_err(|message| LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message,
            })?;
        match directive.kind {
            DirectiveKind::LemmaCall => {
                let contract = typed_lemma_call(
                    &directive.expr,
                    &directive.span_text,
                    lemma_defs,
                    pure_fns,
                    enum_defs,
                    &mut body_type_scope,
                    &local_tys,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?;
                typed_lemma_calls.insert(directive.span_text.clone(), contract);
            }
            _ => {
                let typed = typed_body_expr(
                    &directive.expr,
                    pure_fns,
                    enum_defs,
                    directive.kind,
                    &mut body_type_scope,
                    &local_tys,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?;
                typed_body_exprs.insert(directive.span_text.clone(), typed);
            }
        }
    }
    let typed_ens = match ens_directive {
        Some(directive) => {
            let mut scope = SpecScope::default();
            if let Some(req) = req_directive {
                let _ = typed_contract_expr(
                    &req.expr,
                    pure_fns,
                    enum_defs,
                    &mut scope,
                    &param_tys,
                    false,
                    &result_ty,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: req.span,
                    display_span: Some(req.span_text.clone()),
                    message,
                })?;
            }
            Some(
                typed_contract_expr(
                    &directive.expr,
                    pure_fns,
                    enum_defs,
                    &mut scope,
                    &param_tys,
                    true,
                    &result_ty,
                    &mut inferred,
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?,
            )
        }
        None => None,
    };
    let function_contract = match (req_directive, ens_directive) {
        (None, None) => Some(FunctionContract {
            params: params.clone(),
            req: TypedExpr {
                ty: SpecTy::Bool,
                kind: TypedExprKind::Bool(true),
            },
            req_span: def_span.clone(),
            ens: TypedExpr {
                ty: SpecTy::Bool,
                kind: TypedExprKind::Bool(true),
            },
            ens_span: def_span,
            spec_vars: Vec::new(),
            result,
        }),
        (Some(req), Some(ens)) => Some(FunctionContract {
            params: params.clone(),
            req: typed_req.expect("typed req"),
            req_span: req.span_text.clone(),
            ens: typed_ens.expect("typed ens"),
            ens_span: ens.span_text.clone(),
            spec_vars: contract_scope
                .typed_ordered(&mut inferred)
                .map_err(|message| LoopPrepassError {
                    span: tcx.def_span(def_id.to_def_id()),
                    display_span: None,
                    message,
                })?,
            result,
        }),
        _ => {
            return Err(LoopPrepassError {
                span: tcx.def_span(def_id.to_def_id()),
                display_span: None,
                message: "function contract requires exactly one //@ req and one //@ ens"
                    .to_owned(),
            });
        }
    };
    let loop_contracts =
        collect_loop_contracts(tcx, body, &directives, &resolved_exprs, &typed_body_exprs)?;
    let mut control_point_directives = ControlPointDirectives::empty();
    let mut lowered = Vec::with_capacity(directives.directives.len());

    for directive in directives.directives {
        match directive.kind {
            DirectiveKind::Req => lowered.push(LoweredDirective {
                span: directive.span,
                span_text: directive.span_text,
                kind: directive.kind,
                target: LoweredDirectiveTarget::FunctionEntry,
                expr: directive.expr,
            }),
            DirectiveKind::Ens => lowered.push(LoweredDirective {
                span: directive.span,
                span_text: directive.span_text,
                kind: directive.kind,
                target: LoweredDirectiveTarget::FunctionExit,
                expr: directive.expr,
            }),
            DirectiveKind::Assert => {
                let control = control_point_after(body, directive_anchor_span(&directive.attach))
                    .ok_or_else(|| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message: format!(
                        "unable to map //@ assert at {} to MIR",
                        tcx.sess
                            .source_map()
                            .span_to_diagnostic_string(directive.span)
                    ),
                })?;
                let resolution = resolved_exprs
                    .get(&directive.span_text)
                    .cloned()
                    .expect("resolved assertion expression");
                control_point_directives
                    .by_control_point
                    .entry(control)
                    .or_default()
                    .push(ControlPointDirective::Assert(AssertionContract {
                        assertion: typed_body_exprs
                            .get(&directive.span_text)
                            .cloned()
                            .expect("typed assertion expression"),
                        resolution,
                        assertion_span: directive.span_text.clone(),
                    }));
                lowered.push(LoweredDirective {
                    span: directive.span,
                    span_text: directive.span_text,
                    kind: directive.kind,
                    target: LoweredDirectiveTarget::ControlPoint(control.0, control.1),
                    expr: directive.expr,
                });
            }
            DirectiveKind::Assume => {
                let control = control_point_after(body, directive_anchor_span(&directive.attach))
                    .ok_or_else(|| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message: format!(
                        "unable to map //@ assume at {} to MIR",
                        tcx.sess
                            .source_map()
                            .span_to_diagnostic_string(directive.span)
                    ),
                })?;
                let resolution = resolved_exprs
                    .get(&directive.span_text)
                    .cloned()
                    .expect("resolved assumption expression");
                control_point_directives
                    .by_control_point
                    .entry(control)
                    .or_default()
                    .push(ControlPointDirective::Assume(AssumptionContract {
                        assumption: typed_body_exprs
                            .get(&directive.span_text)
                            .cloned()
                            .expect("typed assumption expression"),
                        resolution,
                    }));
                lowered.push(LoweredDirective {
                    span: directive.span,
                    span_text: directive.span_text,
                    kind: directive.kind,
                    target: LoweredDirectiveTarget::ControlPoint(control.0, control.1),
                    expr: directive.expr,
                });
            }
            DirectiveKind::Inv => {
                let Some(contract) = loop_contracts
                    .by_header
                    .values()
                    .find(|contract| contract.invariant_span == directive.span_text)
                else {
                    continue;
                };
                lowered.push(LoweredDirective {
                    span: directive.span,
                    span_text: directive.span_text,
                    kind: directive.kind,
                    target: LoweredDirectiveTarget::Loop {
                        header: contract.header,
                        invariant_block: contract.invariant_block,
                    },
                    expr: directive.expr,
                });
            }
            DirectiveKind::LemmaCall => {
                let control = control_point_after(body, directive_anchor_span(&directive.attach))
                    .ok_or_else(|| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message: format!(
                        "unable to map //@ lemma call at {} to MIR",
                        tcx.sess
                            .source_map()
                            .span_to_diagnostic_string(directive.span)
                    ),
                })?;
                let resolution = resolved_exprs
                    .get(&directive.span_text)
                    .cloned()
                    .expect("resolved lemma call expression");
                let mut contract = typed_lemma_calls
                    .get(&directive.span_text)
                    .cloned()
                    .expect("typed lemma call expression");
                contract.resolution = resolution;
                control_point_directives
                    .by_control_point
                    .entry(control)
                    .or_default()
                    .push(ControlPointDirective::LemmaCall(contract));
                lowered.push(LoweredDirective {
                    span: directive.span,
                    span_text: directive.span_text,
                    kind: directive.kind,
                    target: LoweredDirectiveTarget::ControlPoint(control.0, control.1),
                    expr: directive.expr,
                });
            }
        }
    }

    Ok(DirectivePrepass {
        directives: lowered,
        loop_contracts,
        control_point_directives,
        function_contract,
        spec_vars: body_scope
            .typed_ordered_with(&contract_scope, &mut inferred)
            .map_err(|message| LoopPrepassError {
                span: tcx.def_span(def_id.to_def_id()),
                display_span: None,
                message,
            })?,
    })
}

#[allow(clippy::too_many_arguments)]
fn resolve_lemma_call_expr_env(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    lemmas: &HashMap<String, LemmaDef>,
    spec_scope: &mut SpecScope,
) -> Result<ResolvedExprEnv, LoopPrepassError> {
    let (lemma_name, args) = lemma_call_parts(expr).map_err(|message| LoopPrepassError {
        span,
        display_span: None,
        message,
    })?;
    if !lemmas.contains_key(lemma_name) {
        return Err(LoopPrepassError {
            span,
            display_span: None,
            message: format!("unknown lemma `{lemma_name}`"),
        });
    }
    let mut resolved = ResolvedExprEnv::default();
    for arg in args {
        let arg_env = resolve_expr_env(
            arg,
            pure_fns,
            enum_defs,
            binding_info,
            hir_locals,
            span,
            anchor_span,
            DirectiveKind::LemmaCall,
            spec_scope,
        )?;
        resolved.locals.extend(arg_env.locals);
        resolved.spec_vars.extend(arg_env.spec_vars);
    }
    Ok(resolved)
}

fn infer_lemma_call(
    expr: &Expr,
    lemmas: &HashMap<String, LemmaDef>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    let (lemma_name, args) = lemma_call_parts(expr)?;
    let lemma = lemmas
        .get(lemma_name)
        .ok_or_else(|| format!("unknown lemma `{lemma_name}`"))?;
    if lemma.params.len() != args.len() {
        return Err(format!(
            "lemma `{lemma_name}` expects {} arguments, found {}",
            lemma.params.len(),
            args.len()
        ));
    }
    for (arg, param) in args.iter().zip(&lemma.params) {
        let arg_ty = infer_body_expr_types(
            arg,
            pure_fns,
            enum_defs,
            DirectiveKind::LemmaCall,
            spec_scope,
            local_tys,
            inferred,
        )?;
        constrain_expr_ty(inferred, &arg_ty, &param.ty)?;
    }
    Ok(())
}

fn typed_lemma_call(
    expr: &Expr,
    span_text: &str,
    lemmas: &HashMap<String, LemmaDef>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<LemmaCallContract, String> {
    let (lemma_name, args) = lemma_call_parts(expr)?;
    let lemma = lemmas
        .get(lemma_name)
        .ok_or_else(|| format!("unknown lemma `{lemma_name}`"))?;
    if lemma.params.len() != args.len() {
        return Err(format!(
            "lemma `{lemma_name}` expects {} arguments, found {}",
            lemma.params.len(),
            args.len()
        ));
    }
    let mut typed_args = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&lemma.params) {
        let typed = typed_body_expr(
            arg,
            pure_fns,
            enum_defs,
            DirectiveKind::LemmaCall,
            spec_scope,
            local_tys,
            inferred,
        )?;
        let unified = unify_spec_tys(&typed.ty, &param.ty)?;
        if unified != param.ty {
            return Err(format!(
                "lemma `{lemma_name}` parameter `{}` expects `{}`, found `{}`",
                param.name,
                display_spec_ty(&param.ty),
                display_spec_ty(&typed.ty)
            ));
        }
        typed_args.push(typed);
    }
    Ok(LemmaCallContract {
        lemma_name: lemma_name.to_owned(),
        args: typed_args,
        resolution: ResolvedExprEnv::default(),
        span_text: span_text.to_owned(),
    })
}

fn type_pure_fns(
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    span: Span,
) -> Result<HashMap<String, TypedPureFnDef>, LoopPrepassError> {
    let mut typed = HashMap::new();
    for def in pure_fns.values() {
        let param_tys: HashMap<_, _> = def
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        let params = def
            .params
            .iter()
            .map(|param| ContractParam {
                name: param.name.clone(),
                ty: param.ty.clone(),
            })
            .collect::<Vec<_>>();
        let mut inferred = SpecTypeInference::default();
        let mut infer_scope = SpecScope::default();
        infer_contract_expr_types(
            &def.body,
            pure_fns,
            enum_defs,
            &mut infer_scope,
            &param_tys,
            false,
            &def.result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("pure function `{}` body: {message}", def.name),
        })?;
        let mut type_scope = SpecScope::default();
        let body = typed_contract_expr(
            &def.body,
            pure_fns,
            enum_defs,
            &mut type_scope,
            &param_tys,
            false,
            &def.result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("pure function `{}` body: {message}", def.name),
        })?;
        let unified =
            unify_spec_tys(&body.ty, &def.result_ty).map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!("pure function `{}` body: {message}", def.name),
            })?;
        if unified != def.result_ty {
            return Err(LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "pure function `{}` body returns `{}`, expected `{}`",
                    def.name,
                    display_spec_ty(&body.ty),
                    display_spec_ty(&def.result_ty)
                ),
            });
        }
        let spec_vars =
            type_scope
                .typed_ordered(&mut inferred)
                .map_err(|message| LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!("pure function `{}` body: {message}", def.name),
                })?;
        if !spec_vars.is_empty() {
            return Err(LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "pure function `{}` body cannot introduce spec variables",
                    def.name
                ),
            });
        }
        typed.insert(
            def.name.clone(),
            TypedPureFnDef {
                name: def.name.clone(),
                params,
                result_ty: def.result_ty.clone(),
                body,
            },
        );
    }
    Ok(typed)
}

fn type_lemmas(
    lemmas: &HashMap<String, LemmaDef>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    span: Span,
) -> Result<HashMap<String, TypedLemmaDef>, LoopPrepassError> {
    let mut typed = HashMap::new();
    for lemma in lemmas.values() {
        let param_tys: HashMap<_, _> = lemma
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        let params = lemma
            .params
            .iter()
            .map(|param| ContractParam {
                name: param.name.clone(),
                ty: param.ty.clone(),
            })
            .collect::<Vec<_>>();
        let result_ty = SpecTy::Bool;
        let mut inferred = SpecTypeInference::default();
        let mut infer_scope = SpecScope::default();
        infer_contract_expr_types(
            &lemma.req,
            pure_fns,
            enum_defs,
            &mut infer_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` req: {message}", lemma.name),
        })?;
        let mut body_infer_scope = infer_scope.clone();
        for stmt in &lemma.body {
            match stmt {
                crate::spec::GhostStmt::Assert(expr) => {
                    infer_contract_expr_types(
                        expr,
                        pure_fns,
                        enum_defs,
                        &mut body_infer_scope,
                        &param_tys,
                        false,
                        &result_ty,
                        &mut inferred,
                    )
                    .map_err(|message| LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!("lemma `{}` body: {message}", lemma.name),
                    })?;
                }
                crate::spec::GhostStmt::Assume(expr) => {
                    infer_contract_expr_types(
                        expr,
                        pure_fns,
                        enum_defs,
                        &mut body_infer_scope,
                        &param_tys,
                        false,
                        &result_ty,
                        &mut inferred,
                    )
                    .map_err(|message| LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!("lemma `{}` body: {message}", lemma.name),
                    })?;
                }
                crate::spec::GhostStmt::Call { name, args } => {
                    let callee = lemmas.get(name).ok_or_else(|| LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!(
                            "lemma `{}` body references unknown lemma `{name}`",
                            lemma.name
                        ),
                    })?;
                    if callee.params.len() != args.len() {
                        return Err(LoopPrepassError {
                            span,
                            display_span: None,
                            message: format!(
                                "lemma `{}` body calls `{name}` with {} arguments; expected {}",
                                lemma.name,
                                args.len(),
                                callee.params.len()
                            ),
                        });
                    }
                    for (arg, param) in args.iter().zip(&callee.params) {
                        let arg_ty = infer_contract_expr_types(
                            arg,
                            pure_fns,
                            enum_defs,
                            &mut body_infer_scope,
                            &param_tys,
                            false,
                            &result_ty,
                            &mut inferred,
                        )
                        .map_err(|message| LoopPrepassError {
                            span,
                            display_span: None,
                            message: format!("lemma `{}` body: {message}", lemma.name),
                        })?;
                        constrain_expr_ty(&mut inferred, &arg_ty, &param.ty).map_err(
                            |message| LoopPrepassError {
                                span,
                                display_span: None,
                                message: format!("lemma `{}` body: {message}", lemma.name),
                            },
                        )?;
                    }
                }
            }
        }
        infer_contract_expr_types(
            &lemma.ens,
            pure_fns,
            enum_defs,
            &mut body_infer_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` ens: {message}", lemma.name),
        })?;

        let mut type_scope = SpecScope::default();
        let req = typed_contract_expr(
            &lemma.req,
            pure_fns,
            enum_defs,
            &mut type_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` req: {message}", lemma.name),
        })?;
        let mut body = Vec::with_capacity(lemma.body.len());
        for stmt in &lemma.body {
            match stmt {
                crate::spec::GhostStmt::Assert(expr) => {
                    let typed_expr = typed_contract_expr(
                        expr,
                        pure_fns,
                        enum_defs,
                        &mut type_scope,
                        &param_tys,
                        false,
                        &result_ty,
                        &mut inferred,
                    )
                    .map_err(|message| LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!("lemma `{}` body: {message}", lemma.name),
                    })?;
                    body.push(TypedGhostStmt::Assert(typed_expr));
                }
                crate::spec::GhostStmt::Assume(expr) => {
                    let typed_expr = typed_contract_expr(
                        expr,
                        pure_fns,
                        enum_defs,
                        &mut type_scope,
                        &param_tys,
                        false,
                        &result_ty,
                        &mut inferred,
                    )
                    .map_err(|message| LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!("lemma `{}` body: {message}", lemma.name),
                    })?;
                    body.push(TypedGhostStmt::Assume(typed_expr));
                }
                crate::spec::GhostStmt::Call { name, args } => {
                    let callee = lemmas.get(name).ok_or_else(|| LoopPrepassError {
                        span,
                        display_span: None,
                        message: format!(
                            "lemma `{}` body references unknown lemma `{name}`",
                            lemma.name
                        ),
                    })?;
                    let mut typed_args = Vec::with_capacity(args.len());
                    for (arg, param) in args.iter().zip(&callee.params) {
                        let typed_arg = typed_contract_expr(
                            arg,
                            pure_fns,
                            enum_defs,
                            &mut type_scope,
                            &param_tys,
                            false,
                            &result_ty,
                            &mut inferred,
                        )
                        .map_err(|message| LoopPrepassError {
                            span,
                            display_span: None,
                            message: format!("lemma `{}` body: {message}", lemma.name),
                        })?;
                        let unified =
                            unify_spec_tys(&typed_arg.ty, &param.ty).map_err(|message| {
                                LoopPrepassError {
                                    span,
                                    display_span: None,
                                    message: format!("lemma `{}` body: {message}", lemma.name),
                                }
                            })?;
                        if unified != param.ty {
                            return Err(LoopPrepassError {
                                span,
                                display_span: None,
                                message: format!(
                                    "lemma `{}` body calls `{name}` with `{}` for parameter `{}` of type `{}`",
                                    lemma.name,
                                    display_spec_ty(&typed_arg.ty),
                                    param.name,
                                    display_spec_ty(&param.ty)
                                ),
                            });
                        }
                        typed_args.push(typed_arg);
                    }
                    body.push(TypedGhostStmt::Call {
                        lemma_name: name.clone(),
                        args: typed_args,
                    });
                }
            }
        }
        let ens = typed_contract_expr(
            &lemma.ens,
            pure_fns,
            enum_defs,
            &mut type_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` ens: {message}", lemma.name),
        })?;
        let spec_vars =
            type_scope
                .typed_ordered(&mut inferred)
                .map_err(|message| LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!("lemma `{}`: {message}", lemma.name),
                })?;
        typed.insert(
            lemma.name.clone(),
            TypedLemmaDef {
                name: lemma.name.clone(),
                params,
                req,
                ens,
                body,
                spec_vars,
            },
        );
    }
    Ok(typed)
}

fn order_pure_fns(
    pure_fns: &HashMap<String, TypedPureFnDef>,
    declaration_order: &[String],
) -> Vec<TypedPureFnDef> {
    let mut ordered = Vec::new();
    let mut visiting = HashSet::new();
    let mut visited = HashSet::new();
    for name in declaration_order {
        visit_pure_fn(name, pure_fns, &mut visiting, &mut visited, &mut ordered);
    }
    ordered
}

fn visit_pure_fn(
    name: &str,
    pure_fns: &HashMap<String, TypedPureFnDef>,
    visiting: &mut HashSet<String>,
    visited: &mut HashSet<String>,
    ordered: &mut Vec<TypedPureFnDef>,
) {
    if visited.contains(name) || !visiting.insert(name.to_owned()) {
        return;
    }
    if let Some(pure_fn) = pure_fns.get(name) {
        visit_pure_fn_expr(&pure_fn.body, pure_fns, visiting, visited, ordered);
    }
    visiting.remove(name);
    if visited.insert(name.to_owned()) {
        ordered.push(pure_fns.get(name).expect("typed pure fn").clone());
    }
}

fn visit_pure_fn_expr(
    expr: &TypedExpr,
    pure_fns: &HashMap<String, TypedPureFnDef>,
    visiting: &mut HashSet<String>,
    visited: &mut HashSet<String>,
    ordered: &mut Vec<TypedPureFnDef>,
) {
    match &expr.kind {
        TypedExprKind::PureCall { func, args } => {
            visit_pure_fn(func, pure_fns, visiting, visited, ordered);
            for arg in args {
                visit_pure_fn_expr(arg, pure_fns, visiting, visited, ordered);
            }
        }
        TypedExprKind::CtorCall { args, .. } => {
            for arg in args {
                visit_pure_fn_expr(arg, pure_fns, visiting, visited, ordered);
            }
        }
        TypedExprKind::Field { base, .. }
        | TypedExprKind::TupleField { base, .. }
        | TypedExprKind::Deref { base }
        | TypedExprKind::Fin { base }
        | TypedExprKind::Unary { arg: base, .. } => {
            visit_pure_fn_expr(base, pure_fns, visiting, visited, ordered);
        }
        TypedExprKind::Binary { lhs, rhs, .. } => {
            visit_pure_fn_expr(lhs, pure_fns, visiting, visited, ordered);
            visit_pure_fn_expr(rhs, pure_fns, visiting, visited, ordered);
        }
        TypedExprKind::Bool(_)
        | TypedExprKind::Int(_)
        | TypedExprKind::Var(_)
        | TypedExprKind::Bind(_) => {}
    }
}

fn order_lemmas(
    lemmas: &HashMap<String, TypedLemmaDef>,
    declaration_order: &[String],
) -> Vec<TypedLemmaDef> {
    let mut ordered = Vec::new();
    let mut visiting = HashSet::new();
    let mut visited = HashSet::new();
    for name in declaration_order {
        visit_lemma(name, lemmas, &mut visiting, &mut visited, &mut ordered);
    }
    ordered
}

fn visit_lemma(
    name: &str,
    lemmas: &HashMap<String, TypedLemmaDef>,
    visiting: &mut HashSet<String>,
    visited: &mut HashSet<String>,
    ordered: &mut Vec<TypedLemmaDef>,
) {
    if visited.contains(name) || !visiting.insert(name.to_owned()) {
        return;
    }
    if let Some(lemma) = lemmas.get(name) {
        for stmt in &lemma.body {
            if let TypedGhostStmt::Call { lemma_name, .. } = stmt {
                visit_lemma(lemma_name, lemmas, visiting, visited, ordered);
            }
        }
    }
    visiting.remove(name);
    if visited.insert(name.to_owned()) {
        ordered.push(lemmas.get(name).expect("typed lemma").clone());
    }
}

fn lemma_call_parts(expr: &Expr) -> Result<(&str, &[Expr]), String> {
    match expr {
        Expr::Call { func, args } => Ok((func, args)),
        _ => Err("lemma call must be of the form `name(args...)`".to_owned()),
    }
}

fn directive_error_to_prepass(err: DirectiveError) -> LoopPrepassError {
    LoopPrepassError {
        span: err.span,
        display_span: None,
        message: err.message,
    }
}

pub fn collect_hir_binding_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Result<HirBindingInfo, LoopPrepassError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut collector = HirBindingSpanCollector {
        info: HirBindingInfo::default(),
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => Ok(collector.info),
        ControlFlow::Break(err) => Err(err),
    }
}

fn spans_match<'tcx>(tcx: TyCtxt<'tcx>, left: Span, right: Span) -> bool {
    left == right
        || tcx.sess.source_map().stmt_span(left, right) == right
        || tcx.sess.source_map().stmt_span(right, left) == left
}

fn control_point_after<'tcx>(body: &Body<'tcx>, span: Span) -> Option<(BasicBlock, usize)> {
    let mut target: Option<(BasicBlock, usize, Span)> = None;
    for (basic_block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let candidate_span = statement.source_info.span;
            if candidate_span.lo() < span.lo() {
                continue;
            }
            if target
                .as_ref()
                .is_none_or(|(_, _, best_span)| candidate_span.lo() < best_span.lo())
            {
                target = Some((basic_block, statement_index, candidate_span));
            }
        }
        let candidate_span = data.terminator().source_info.span;
        if candidate_span.lo() < span.lo() {
            continue;
        }
        if target
            .as_ref()
            .is_none_or(|(_, _, best_span)| candidate_span.lo() < best_span.lo())
        {
            target = Some((basic_block, data.statements.len(), candidate_span));
        }
    }
    target.map(|(basic_block, statement_index, _)| (basic_block, statement_index))
}

fn collect_loop_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    directives: &CollectedFunctionDirectives,
    resolved_exprs: &HashMap<String, ResolvedExprEnv>,
    typed_exprs: &HashMap<String, TypedExpr>,
) -> Result<LoopContracts, LoopPrepassError> {
    let preds = body.basic_blocks.predecessors();
    let doms = body.basic_blocks.dominators();
    let mut loops = HashMap::new();
    for (latch, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else {
            continue;
        };
        for header in term.successors() {
            if doms.dominates(header, latch) {
                let body_blocks = natural_loop(|bb| preds[bb].iter().copied(), latch, header);
                let written_locals = written_locals(body, &body_blocks);
                let exit_blocks = loop_exits(body, &body_blocks);
                loops
                    .entry(header)
                    .and_modify(|info: &mut LoopContract| {
                        info.body_blocks.extend(body_blocks.iter().copied());
                        info.exit_blocks.extend(exit_blocks.iter().copied());
                        info.written_locals.extend(written_locals.iter().copied());
                    })
                    .or_insert(LoopContract {
                        header,
                        hir_loop_id: HirId::INVALID,
                        invariant_block: header,
                        invariant: TypedExpr {
                            ty: SpecTy::Bool,
                            kind: TypedExprKind::Bool(true),
                        },
                        resolution: ResolvedExprEnv::default(),
                        invariant_span: tcx.sess.source_map().span_to_diagnostic_string(
                            body.basic_blocks[header].terminator().source_info.span,
                        ),
                        body_blocks,
                        exit_blocks,
                        written_locals,
                    });
            }
        }
    }

    let headers: Vec<_> = loops.keys().copied().collect();
    for directive in directives
        .directives
        .iter()
        .filter(|directive| directive.kind == DirectiveKind::Inv)
    {
        let DirectiveAttach::Loop {
            loop_expr_id,
            loop_span,
            body_span,
            entry_span: directive_entry_span,
        } = directive.attach
        else {
            continue;
        };
        let Some(header) = headers
            .iter()
            .copied()
            .filter(|header| {
                let loop_info = &loops[header];
                let header_span = body.basic_blocks[*header].terminator().source_info.span;
                let entry_span = loop_entry_anchor_span(body, loop_info).unwrap_or(header_span);
                span_contains(loop_span, header_span) || span_contains(body_span, entry_span)
            })
            .min_by_key(|header| {
                let loop_info = &loops[header];
                let header_span = body.basic_blocks[*header].terminator().source_info.span;
                let entry_span = loop_entry_anchor_span(body, loop_info).unwrap_or(header_span);
                (
                    !spans_match(tcx, directive_entry_span, entry_span),
                    loop_info.body_blocks.len(),
                )
            })
        else {
            continue;
        };
        let loop_info = &loops[&header];
        let invariant_block = loop_info
            .body_blocks
            .iter()
            .copied()
            .filter(|block| *block != header)
            .min_by_key(|block| (loop_entry_distance(body, loop_info, *block), block.index()))
            .unwrap_or(header);
        let resolution = resolved_exprs
            .get(&directive.span_text)
            .cloned()
            .expect("resolved invariant expression");
        let loop_contract = loops.get_mut(&header).expect("loop info present");
        loop_contract.hir_loop_id = loop_expr_id;
        loop_contract.invariant_block = invariant_block;
        loop_contract.invariant = typed_exprs
            .get(&directive.span_text)
            .cloned()
            .expect("typed invariant expression");
        loop_contract.resolution = resolution;
        loop_contract.invariant_span = directive.span_text.clone();
    }

    for header in &headers {
        if loops[header].hir_loop_id == HirId::INVALID {
            return Err(LoopPrepassError {
                span: body.basic_blocks[*header].terminator().source_info.span,
                display_span: None,
                message: format!(
                    "loop at bb{} requires exactly one //@ inv before the body",
                    header.index()
                ),
            });
        }
    }

    let by_invariant_block = loops
        .iter()
        .map(|(header, contract)| (contract.invariant_block, *header))
        .collect();

    Ok(LoopContracts {
        by_header: loops,
        by_invariant_block,
    })
}

fn collect_ghost_items_in_source(
    source: &str,
    error_span: Span,
    enums: &mut Vec<EnumDef>,
    pure_fns: &mut Vec<PureFnDef>,
    lemmas: &mut Vec<LemmaDef>,
) -> Result<(), LoopPrepassError> {
    let mut cursor = 0usize;
    while let Some(start) = source[cursor..].find("/*@") {
        let start = cursor + start;
        let body_start = start + 3;
        let Some(end_rel) = source[body_start..].find("*/") else {
            return Err(LoopPrepassError {
                span: error_span,
                display_span: None,
                message: "unclosed /*@ ghost block".to_owned(),
            });
        };
        let end = body_start + end_rel;
        let block = &source[body_start..end];
        let parsed = parse_ghost_block(block).map_err(|err| LoopPrepassError {
            span: error_span,
            display_span: None,
            message: err.to_string(),
        })?;
        enums.extend(parsed.enums);
        pure_fns.extend(parsed.pure_fns);
        lemmas.extend(parsed.lemmas);
        cursor = end + 2;
    }
    Ok(())
}

fn validate_function_contract_expr_prepass(
    span: Span,
    span_text: &str,
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), LoopPrepassError> {
    validate_contract_expr_core(expr, pure_fns, enum_defs, spec_scope, params, allow_result)
        .map_err(|message| LoopPrepassError {
            span,
            display_span: Some(span_text.to_owned()),
            message,
        })
}

fn validate_contract_expr_core(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &[String],
    allow_result: bool,
) -> Result<(), String> {
    match expr {
        Expr::Bool(_) | Expr::Int(_) => Ok(()),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name)
                || params.iter().any(|param| param == name)
                || (allow_result && name == "result")
            {
                return Ok(());
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::Bind(name) => spec_scope
            .bind(
                name,
                Span::default(),
                None,
                if allow_result { "ens" } else { "req" },
            )
            .map_err(|err| err.message),
        Expr::Call { func, args } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                let ctor = &enum_def.ctors[ctor_index];
                if ctor.fields.len() != args.len() {
                    return Err(format!(
                        "constructor `{func}` expects {} arguments, found {}",
                        ctor.fields.len(),
                        args.len()
                    ));
                }
            } else {
                let Some(def) = pure_fns.get(func) else {
                    return Err(format!("unknown pure function `{func}`"));
                };
                if def.params.len() != args.len() {
                    return Err(format!(
                        "pure function `{func}` expects {} arguments, found {}",
                        def.params.len(),
                        args.len()
                    ));
                }
            }
            for arg in args {
                validate_contract_expr_core(
                    arg,
                    pure_fns,
                    enum_defs,
                    spec_scope,
                    params,
                    allow_result,
                )?;
            }
            Ok(())
        }
        Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Deref { base } => {
            validate_contract_expr_core(base, pure_fns, enum_defs, spec_scope, params, allow_result)
        }
        Expr::Unary { arg, .. } => {
            validate_contract_expr_core(arg, pure_fns, enum_defs, spec_scope, params, allow_result)
        }
        Expr::Binary { lhs, rhs, .. } => {
            validate_contract_expr_core(
                lhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
            )?;
            validate_contract_expr_core(rhs, pure_fns, enum_defs, spec_scope, params, allow_result)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_expr_env(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
) -> Result<ResolvedExprEnv, LoopPrepassError> {
    let mut resolved = ResolvedExprEnv::default();
    let mut ctx = ExprResolutionContext {
        pure_fns,
        enum_defs,
        binding_info,
        hir_locals,
        span,
        anchor_span,
        kind,
        spec_scope,
    };
    resolve_expr_env_into(expr, &mut ctx, &mut resolved)?;
    Ok(resolved)
}

fn resolve_expr_env_into(
    expr: &Expr,
    ctx: &mut ExprResolutionContext<'_>,
    resolved: &mut ResolvedExprEnv,
) -> Result<(), LoopPrepassError> {
    match expr {
        Expr::Bool(_) | Expr::Int(_) => Ok(()),
        Expr::Var(name) => {
            if ctx.spec_scope.visible.contains(name) {
                resolved.spec_vars.insert(name.clone());
                return Ok(());
            }
            let symbol = Symbol::intern(name);
            let Some(hir_id) = resolve_binding_hir_id(ctx.binding_info, symbol, ctx.anchor_span)
            else {
                return Err(LoopPrepassError {
                    span: ctx.span,
                    display_span: None,
                    message: format!("unresolved binding `{name}` in //@ {}", ctx.kind.keyword()),
                });
            };
            let Some(local) = ctx.hir_locals.get(&hir_id).copied() else {
                return Err(LoopPrepassError {
                    span: ctx.anchor_span,
                    display_span: None,
                    message: format!("missing MIR local for HIR id {:?}", hir_id),
                });
            };
            resolved.locals.insert(name.clone(), local);
            Ok(())
        }
        Expr::Bind(name) => {
            ctx.spec_scope
                .bind(name, ctx.span, None, ctx.kind.keyword())?;
            resolved.spec_vars.insert(name.clone());
            Ok(())
        }
        Expr::Call { func, args } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(ctx.enum_defs, func) {
                let ctor = &enum_def.ctors[ctor_index];
                if ctor.fields.len() != args.len() {
                    return Err(LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message: format!(
                            "constructor `{func}` expects {} arguments, found {}",
                            ctor.fields.len(),
                            args.len()
                        ),
                    });
                }
            } else {
                let Some(def) = ctx.pure_fns.get(func) else {
                    return Err(LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message: format!("unknown pure function `{func}`"),
                    });
                };
                if def.params.len() != args.len() {
                    return Err(LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message: format!(
                            "pure function `{func}` expects {} arguments, found {}",
                            def.params.len(),
                            args.len()
                        ),
                    });
                }
            }
            for arg in args {
                resolve_expr_env_into(arg, ctx, resolved)?;
            }
            Ok(())
        }
        Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Deref { base } => {
            resolve_expr_env_into(base, ctx, resolved)
        }
        Expr::Unary { arg, .. } => resolve_expr_env_into(arg, ctx, resolved),
        Expr::Binary { lhs, rhs, .. } => {
            resolve_expr_env_into(lhs, ctx, resolved)?;
            resolve_expr_env_into(rhs, ctx, resolved)
        }
    }
}

fn resolve_binding_hir_id(
    binding_info: &HirBindingInfo,
    name: Symbol,
    anchor_span: Span,
) -> Option<HirId> {
    binding_info.by_name.get(&name).and_then(|bindings| {
        bindings
            .iter()
            .filter(|(_, span)| span.lo() < anchor_span.lo())
            .max_by_key(|(_, span)| span.lo())
            .map(|(hir_id, _)| *hir_id)
    })
}

fn directive_anchor_span(attach: &DirectiveAttach) -> Span {
    match attach {
        DirectiveAttach::Function => Span::default(),
        DirectiveAttach::Statement { anchor_span } => *anchor_span,
        DirectiveAttach::Loop { entry_span, .. } => *entry_span,
    }
}

struct HirBindingSpanCollector {
    info: HirBindingInfo,
}

impl<'tcx> Visitor<'tcx> for HirBindingSpanCollector {
    type NestedFilter = intravisit::nested_filter::None;
    type Result = ControlFlow<LoopPrepassError>;

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) -> Self::Result {
        if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
            self.info.spans.entry(hir_id).or_insert(pat.span);
            self.info
                .by_name
                .entry(ident.name)
                .or_default()
                .push((hir_id, pat.span));
        }
        intravisit::walk_pat(self, pat)
    }
}

fn loop_entry_distance<'tcx>(
    body: &Body<'tcx>,
    loop_info: &LoopContract,
    target: BasicBlock,
) -> usize {
    let mut distance = HashMap::from([(loop_info.header, 0usize)]);
    let mut work = VecDeque::from([loop_info.header]);
    while let Some(block) = work.pop_front() {
        let Some(current_distance) = distance.get(&block).copied() else {
            continue;
        };
        let Some(term) = &body.basic_blocks[block].terminator else {
            continue;
        };
        for succ in term.successors() {
            if !loop_info.body_blocks.contains(&succ) || distance.contains_key(&succ) {
                continue;
            }
            distance.insert(succ, current_distance + 1);
            work.push_back(succ);
        }
    }
    distance.get(&target).copied().unwrap_or(usize::MAX)
}

fn loop_entry_anchor_span<'tcx>(body: &Body<'tcx>, loop_info: &LoopContract) -> Option<Span> {
    let mut blocks: Vec<_> = loop_info
        .body_blocks
        .iter()
        .copied()
        .filter(|block| *block != loop_info.header)
        .collect();
    blocks.sort_by_key(|block| (loop_entry_distance(body, loop_info, *block), block.index()));
    for block in blocks {
        if let Some(span) = block_source_span(body, block)
            && !span.is_dummy()
        {
            return Some(span);
        }
    }
    None
}

fn block_source_span<'tcx>(body: &Body<'tcx>, block: BasicBlock) -> Option<Span> {
    let data = &body.basic_blocks[block];
    for stmt in &data.statements {
        if !stmt.source_info.span.is_dummy() {
            return Some(stmt.source_info.span);
        }
    }
    let span = data.terminator().source_info.span;
    if !span.is_dummy() {
        return Some(span);
    }
    None
}

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.lo() <= inner.lo() && inner.hi() <= outer.hi()
}

fn natural_loop<I, F>(preds: F, latch: BasicBlock, header: BasicBlock) -> BTreeSet<BasicBlock>
where
    I: IntoIterator<Item = BasicBlock>,
    F: Fn(BasicBlock) -> I,
{
    let mut work = vec![latch];
    let mut seen = BTreeSet::from([header, latch]);
    while let Some(bb) = work.pop() {
        for pred in preds(bb) {
            if seen.insert(pred) {
                work.push(pred);
            }
        }
    }
    seen
}

fn loop_exits<'tcx>(body: &Body<'tcx>, body_blocks: &BTreeSet<BasicBlock>) -> BTreeSet<BasicBlock> {
    let mut exits = BTreeSet::new();
    for bb in body_blocks {
        let data = &body.basic_blocks[*bb];
        let Some(term) = &data.terminator else {
            continue;
        };
        for succ in term.successors() {
            if !body_blocks.contains(&succ) {
                exits.insert(succ);
            }
        }
    }
    exits
}

fn function_param_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Result<Vec<String>, VerificationResult> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut names = Vec::with_capacity(body.params.len());
    for (index, param) in body.params.iter().enumerate() {
        match param.pat.kind {
            PatKind::Binding(_, _, ident, _) => names.push(ident.name.to_string()),
            _ => {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    &tcx.sess
                        .source_map()
                        .span_to_diagnostic_string(param.pat.span),
                    format!("unsupported function parameter pattern #{index}"),
                ));
            }
        }
    }
    Ok(names)
}

fn function_param_names_relaxed<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Vec<String> {
    let body = tcx.hir_body_owned_by(def_id);
    body.params
        .iter()
        .enumerate()
        .map(|(index, param)| match param.pat.kind {
            PatKind::Binding(_, _, ident, _) => ident.name.to_string(),
            _ => format!("arg{index}"),
        })
        .collect()
}

fn function_contract_signature_with_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    names: Vec<String>,
) -> Result<(Vec<ContractParam>, SpecTy), VerificationResult> {
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let inputs = sig.inputs().skip_binder();
    if inputs.len() != names.len() {
        return Err(function_contract_error(
            tcx,
            def_id,
            &tcx.sess
                .source_map()
                .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id())),
            format!(
                "function signature arity mismatch: names={}, inputs={}",
                names.len(),
                inputs.len()
            ),
        ));
    }
    let params = names
        .into_iter()
        .zip(inputs.iter().copied())
        .map(|(name, ty)| {
            spec_ty_for_rust_ty(tcx, ty)
                .map(|ty| ContractParam { name, ty })
                .map_err(|message| {
                    function_contract_error(
                        tcx,
                        def_id,
                        &tcx.sess
                            .source_map()
                            .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id())),
                        message,
                    )
                })
        })
        .collect::<Result<Vec<_>, VerificationResult>>()?;
    let result = spec_ty_for_rust_ty(tcx, sig.output().skip_binder()).map_err(|message| {
        function_contract_error(
            tcx,
            def_id,
            &tcx.sess
                .source_map()
                .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id())),
            message,
        )
    })?;
    Ok((params, result))
}

fn function_contract_error<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: &str,
    message: String,
) -> VerificationResult {
    VerificationResult {
        function: tcx.def_path_str(def_id.to_def_id()),
        status: VerificationStatus::Unsupported,
        span: span.to_owned(),
        message,
    }
}

fn written_locals<'tcx>(
    body: &Body<'tcx>,
    body_blocks: &BTreeSet<BasicBlock>,
) -> BTreeSet<rustc_middle::mir::Local> {
    let mut written = BTreeSet::new();
    for bb in body_blocks {
        for stmt in &body.basic_blocks[*bb].statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (place, _) = &**assign;
                if let Some(local) = place.as_local() {
                    written.insert(local);
                } else if let Some((base, PlaceElem::Deref)) = place.as_ref().last_projection()
                    && base.projection.is_empty()
                {
                    written.insert(base.local);
                }
            }
        }
        if let Some(term) = &body.basic_blocks[*bb].terminator
            && let TerminatorKind::Call { destination, .. } = &term.kind
        {
            written.insert(destination.local);
        }
    }
    written
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::{Expr, PureFnDef, PureFnParam, SpecTy, TypedExprKind};

    #[test]
    fn preserves_user_pure_call_for_engine_encoding() {
        let pure_fns = HashMap::from([(
            "id".to_owned(),
            PureFnDef {
                name: "id".to_owned(),
                params: vec![PureFnParam {
                    name: "x".to_owned(),
                    ty: SpecTy::I32,
                }],
                result_ty: SpecTy::I32,
                body: Expr::Var("x".to_owned()),
            },
        )]);

        let typed = type_pure_call(
            "id",
            &[Expr::Var("arg".to_owned())],
            &pure_fns,
            &HashMap::new(),
            &mut |expr| {
                assert_eq!(expr, &Expr::Var("arg".to_owned()));
                Ok(TypedExpr {
                    ty: SpecTy::I32,
                    kind: TypedExprKind::Var("arg".to_owned()),
                })
            },
        )
        .expect("typed pure call");

        assert_eq!(
            typed,
            TypedExpr {
                ty: SpecTy::I32,
                kind: TypedExprKind::PureCall {
                    func: "id".to_owned(),
                    args: vec![TypedExpr {
                        ty: SpecTy::I32,
                        kind: TypedExprKind::Var("arg".to_owned()),
                    }],
                },
            }
        );
    }
}
