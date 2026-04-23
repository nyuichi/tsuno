use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::ops::ControlFlow;

use crate::directive::{
    CollectedFunctionDirectives, DirectiveAttach, DirectiveError, DirectiveKind,
    collect_function_directives,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{
    EnumDef, Expr, GhostMatchArm, LemmaDef, MatchBinding, MatchPattern, PureFnDef, SpecTy,
    StructFieldTy, StructTy, TypedExpr, TypedExprKind, TypedMatchArm, TypedMatchBinding,
    parse_ghost_block,
};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{HirId, Pat, PatKind};
use rustc_middle::mir::{BasicBlock, Body, Local, PlaceElem, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::def_id::LocalDefId;
use rustc_span::{DUMMY_SP, Span, Symbol};

const PRELUDE_GHOST_SOURCE: &str = include_str!("../lib/prelude.rs");

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

#[derive(Debug, Clone, Default)]
pub struct LoopContracts {
    pub by_header: HashMap<BasicBlock, LoopContract>,
    pub by_invariant_block: HashMap<BasicBlock, BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct AssertionContract {
    pub assertion: NormalizedPredicate,
    pub resolution: ResolvedExprEnv,
    pub assertion_span: String,
}

#[derive(Debug, Clone)]
pub struct AssumptionContract {
    pub assumption: TypedExpr,
    pub resolution: ResolvedExprEnv,
}

#[derive(Debug, Clone)]
pub struct NormalizedBinding {
    pub name: String,
    pub value: TypedExpr,
}

#[derive(Debug, Clone)]
pub struct NormalizedPredicate {
    pub bindings: Vec<NormalizedBinding>,
    pub condition: TypedExpr,
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

#[derive(Debug, Clone, Default)]
pub struct ControlPointDirectives {
    pub by_control_point: HashMap<(BasicBlock, usize), Vec<ControlPointDirective>>,
}

#[derive(Debug, Clone)]
pub struct TypedPureFnDef {
    pub name: String,
    pub params: Vec<ContractParam>,
    pub body: TypedExpr,
}

#[derive(Debug, Clone)]
pub enum TypedGhostStmt {
    Assert(NormalizedPredicate),
    Assume(TypedExpr),
    Call {
        lemma_name: String,
        args: Vec<TypedExpr>,
    },
    Match {
        scrutinee: TypedExpr,
        arms: Vec<TypedGhostMatchArm>,
        default: Option<Vec<TypedGhostStmt>>,
    },
}

#[derive(Debug, Clone)]
pub struct TypedGhostMatchArm {
    pub ctor_index: usize,
    pub bindings: Vec<TypedMatchBinding>,
    pub body: Vec<TypedGhostStmt>,
}

#[derive(Debug, Clone)]
pub struct TypedLemmaDef {
    pub name: String,
    pub params: Vec<ContractParam>,
    pub req: NormalizedPredicate,
    pub ens: TypedExpr,
    pub body: Vec<TypedGhostStmt>,
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
    pub req: NormalizedPredicate,
    #[allow(dead_code)]
    pub req_span: String,
    pub ens: TypedExpr,
    pub ens_span: String,
    pub result: SpecTy,
}

#[derive(Debug, Clone)]
pub struct DirectivePrepass {
    pub loop_contracts: LoopContracts,
    pub control_point_directives: ControlPointDirectives,
    pub function_contract: Option<FunctionContract>,
}

#[derive(Debug, Clone)]
struct RawGlobalGhostPrepass {
    pub enums: HashMap<String, EnumDef>,
    pub pure_fns: HashMap<String, PureFnDef>,
    pub lemmas: HashMap<String, LemmaDef>,
    pure_fn_order: Vec<String>,
    lemma_order: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct GlobalGhostPrepass {
    pub enums: HashMap<String, EnumDef>,
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
    pub fn contract_by_header(&self, header: BasicBlock) -> Option<&LoopContract> {
        self.by_header.get(&header)
    }

    pub fn header_for_invariant_block(&self, block: BasicBlock) -> Option<BasicBlock> {
        self.by_invariant_block.get(&block).copied()
    }
}

impl ControlPointDirectives {
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

fn compute_function_prepass<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
    ghosts: &RawGlobalGhostPrepass,
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
    let anchor_span = global_ghost_anchor_span(tcx);
    let raw_ghosts = match compute_raw_global_ghost_prepass(tcx, anchor_span) {
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
    let ghosts = match type_global_ghost_prepass(&raw_ghosts, anchor_span) {
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
        match compute_function_prepass(tcx, def_id, item.span, &body.borrow(), &raw_ghosts) {
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

fn global_ghost_anchor_span<'tcx>(tcx: TyCtxt<'tcx>) -> Span {
    tcx.hir_free_items()
        .next()
        .map(|item_id| tcx.hir_item(item_id).span)
        .unwrap_or(DUMMY_SP)
}

fn compute_raw_global_ghost_prepass<'tcx>(
    tcx: TyCtxt<'tcx>,
    anchor_span: Span,
) -> Result<RawGlobalGhostPrepass, LoopPrepassError> {
    let sources = collect_global_ghost_sources(tcx, anchor_span);

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

    Ok(RawGlobalGhostPrepass {
        enums,
        pure_fns,
        lemmas,
        pure_fn_order,
        lemma_order,
    })
}

fn type_global_ghost_prepass(
    raw: &RawGlobalGhostPrepass,
    anchor_span: Span,
) -> Result<GlobalGhostPrepass, LoopPrepassError> {
    let typed_pure_fns = type_pure_fns(&raw.pure_fns, &raw.pure_fn_order, &raw.enums, anchor_span)?;
    let typed_lemmas = type_lemmas(
        &raw.lemmas,
        &raw.lemma_order,
        &raw.pure_fns,
        &raw.enums,
        anchor_span,
    )?;
    Ok(GlobalGhostPrepass {
        enums: raw.enums.clone(),
        typed_pure_fns,
        typed_lemmas,
    })
}

fn collect_global_ghost_sources<'tcx>(tcx: TyCtxt<'tcx>, anchor_span: Span) -> Vec<(Span, String)> {
    let mut sources = vec![(anchor_span, PRELUDE_GHOST_SOURCE.to_owned())];
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
    sources
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

    fn typed_ordered(
        &self,
        inferred: &mut SpecTypeInference,
    ) -> Result<Vec<SpecVarBinding>, String> {
        typed_spec_vars_for_names(&self.ordered, inferred)
    }
}

fn typed_expr_contains_bind(expr: &TypedExpr) -> bool {
    match &expr.kind {
        TypedExprKind::Bind(_) => true,
        TypedExprKind::Bool(_)
        | TypedExprKind::Int(_)
        | TypedExprKind::Var(_)
        | TypedExprKind::RustVar(_) => false,
        TypedExprKind::SeqLit(items) => items.iter().any(typed_expr_contains_bind),
        TypedExprKind::Match {
            scrutinee,
            arms,
            default,
        } => {
            typed_expr_contains_bind(scrutinee)
                || arms.iter().any(|arm| typed_expr_contains_bind(&arm.body))
                || default.as_deref().is_some_and(typed_expr_contains_bind)
        }
        TypedExprKind::PureCall { args, .. } | TypedExprKind::CtorCall { args, .. } => {
            args.iter().any(typed_expr_contains_bind)
        }
        TypedExprKind::Field { base, .. }
        | TypedExprKind::TupleField { base, .. }
        | TypedExprKind::Deref { base }
        | TypedExprKind::Fin { base }
        | TypedExprKind::Unary { arg: base, .. } => typed_expr_contains_bind(base),
        TypedExprKind::Index { base, index } => {
            typed_expr_contains_bind(base) || typed_expr_contains_bind(index)
        }
        TypedExprKind::Binary { lhs, rhs, .. } => {
            typed_expr_contains_bind(lhs) || typed_expr_contains_bind(rhs)
        }
    }
}

fn typed_bool_expr(value: bool) -> TypedExpr {
    TypedExpr {
        ty: SpecTy::Bool,
        kind: TypedExprKind::Bool(value),
    }
}

fn split_top_level_conjuncts(expr: TypedExpr, out: &mut Vec<TypedExpr>) {
    match expr.kind {
        TypedExprKind::Binary {
            op: crate::spec::BinaryOp::And,
            lhs,
            rhs,
        } => {
            split_top_level_conjuncts(*lhs, out);
            split_top_level_conjuncts(*rhs, out);
        }
        _ => out.push(expr),
    }
}

fn join_top_level_conjuncts(exprs: Vec<TypedExpr>) -> TypedExpr {
    exprs
        .into_iter()
        .reduce(|lhs, rhs| TypedExpr {
            ty: SpecTy::Bool,
            kind: TypedExprKind::Binary {
                op: crate::spec::BinaryOp::And,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
        })
        .unwrap_or_else(|| typed_bool_expr(true))
}

fn normalize_assert_like_predicate(
    expr: TypedExpr,
    kind: &str,
) -> Result<NormalizedPredicate, String> {
    let mut conjuncts = Vec::new();
    split_top_level_conjuncts(expr, &mut conjuncts);
    let mut bindings = Vec::new();
    let mut residual = Vec::new();
    for conjunct in conjuncts {
        match conjunct.kind {
            TypedExprKind::Binary {
                op: crate::spec::BinaryOp::Eq,
                lhs,
                rhs,
            } => {
                if let TypedExprKind::Bind(name) = &lhs.kind {
                    if typed_expr_contains_bind(&rhs) {
                        return Err(format!(
                            "spec bindings in {kind} must have the form `?x == value` at the top level"
                        ));
                    }
                    bindings.push(NormalizedBinding {
                        name: name.clone(),
                        value: *rhs,
                    });
                    continue;
                }
                let expr = TypedExpr {
                    ty: SpecTy::Bool,
                    kind: TypedExprKind::Binary {
                        op: crate::spec::BinaryOp::Eq,
                        lhs,
                        rhs,
                    },
                };
                if typed_expr_contains_bind(&expr) {
                    return Err(format!(
                        "spec bindings in {kind} must have the form `?x == value` at the top level"
                    ));
                }
                residual.push(expr);
            }
            _ => {
                if typed_expr_contains_bind(&conjunct) {
                    return Err(format!(
                        "spec bindings in {kind} must have the form `?x == value` at the top level"
                    ));
                }
                residual.push(conjunct);
            }
        }
    }
    Ok(NormalizedPredicate {
        bindings,
        condition: join_top_level_conjuncts(residual),
    })
}

fn ensure_bind_free_predicate(expr: TypedExpr, kind: &str) -> Result<TypedExpr, String> {
    if typed_expr_contains_bind(&expr) {
        return Err(format!("new spec bindings are not allowed in {kind}"));
    }
    Ok(expr)
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
    allow_bare_names: bool,
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
        (SpecTy::Seq(lhs), SpecTy::Seq(rhs)) => {
            Ok(SpecTy::Seq(Box::new(unify_spec_tys(lhs, rhs)?)))
        }
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
        (
            SpecTy::Named {
                name: lhs_name,
                args: lhs_args,
            },
            SpecTy::Named {
                name: rhs_name,
                args: rhs_args,
            },
        ) if lhs_name == rhs_name && lhs_args.len() == rhs_args.len() => {
            let mut args = Vec::with_capacity(lhs_args.len());
            for (lhs_arg, rhs_arg) in lhs_args.iter().zip(rhs_args) {
                args.push(unify_spec_tys(lhs_arg, rhs_arg)?);
            }
            Ok(SpecTy::Named {
                name: lhs_name.clone(),
                args,
            })
        }
        (SpecTy::TypeParam(lhs), SpecTy::TypeParam(rhs)) if lhs == rhs => {
            Ok(SpecTy::TypeParam(lhs.clone()))
        }
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
        SpecTy::Seq(inner) => format!("Seq<{}>", display_spec_ty(inner)),
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
        SpecTy::Named { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}<{}>",
                    name,
                    args.iter()
                        .map(display_spec_ty)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        SpecTy::TypeParam(name) => name.clone(),
    }
}

fn display_spec_field_ty(field: &StructFieldTy) -> String {
    format!("{}.{}", field.name, display_spec_ty(&field.ty))
}

fn nat_spec_ty() -> SpecTy {
    SpecTy::Named {
        name: "Nat".to_owned(),
        args: vec![],
    }
}

fn is_nat_spec_ty(ty: &SpecTy) -> bool {
    matches!(
        ty,
        SpecTy::Named { name, args } if name == "Nat" && args.is_empty()
    )
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
        SpecTy::Named { args, .. } => args.iter().all(is_fully_inferred_spec_ty),
        SpecTy::TypeParam(_) => true,
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
            if tcx.def_path_str(adt_def.did()) == "std::vec::Vec" {
                let Some(inner) = args.types().next() else {
                    return Err(format!("unsupported vector type {ty:?}"));
                };
                return Ok(SpecTy::Seq(Box::new(spec_ty_for_rust_ty(tcx, inner)?)));
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

fn validate_named_spec_ty(
    ty: &SpecTy,
    enum_defs: &HashMap<String, EnumDef>,
    type_params: &HashSet<String>,
) -> Result<(), String> {
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
        SpecTy::Seq(inner) => validate_named_spec_ty(inner, enum_defs, type_params),
        SpecTy::Tuple(items) => {
            for item in items {
                validate_named_spec_ty(item, enum_defs, type_params)?;
            }
            Ok(())
        }
        SpecTy::Struct(struct_ty) => {
            for field in &struct_ty.fields {
                validate_named_spec_ty(&field.ty, enum_defs, type_params)?;
            }
            Ok(())
        }
        SpecTy::Named { name, args } => {
            let Some(enum_def) = enum_defs.get(name) else {
                return Err(format!("unknown spec type `{name}`"));
            };
            if enum_def.type_params.len() != args.len() {
                return Err(format!(
                    "spec type `{name}` expects {} type arguments, found {}",
                    enum_def.type_params.len(),
                    args.len()
                ));
            }
            for arg in args {
                validate_named_spec_ty(arg, enum_defs, type_params)?;
            }
            Ok(())
        }
        SpecTy::TypeParam(name) => type_params
            .contains(name)
            .then_some(())
            .ok_or_else(|| format!("unbound spec type parameter `{name}`")),
        SpecTy::Ref(_) | SpecTy::Mut(_) => {
            Err("Ref<T> and Mut<T> are not supported in spec enum definitions".to_owned())
        }
    }
}

fn enum_result_ty(enum_def: &EnumDef, type_args: Vec<SpecTy>) -> SpecTy {
    SpecTy::Named {
        name: enum_def.name.clone(),
        args: type_args,
    }
}

fn try_instantiate_spec_ty(ty: &SpecTy, bindings: &HashMap<String, SpecTy>) -> Option<SpecTy> {
    match ty {
        SpecTy::Bool => Some(SpecTy::Bool),
        SpecTy::IntLiteral => Some(SpecTy::IntLiteral),
        SpecTy::I8 => Some(SpecTy::I8),
        SpecTy::I16 => Some(SpecTy::I16),
        SpecTy::I32 => Some(SpecTy::I32),
        SpecTy::I64 => Some(SpecTy::I64),
        SpecTy::Isize => Some(SpecTy::Isize),
        SpecTy::U8 => Some(SpecTy::U8),
        SpecTy::U16 => Some(SpecTy::U16),
        SpecTy::U32 => Some(SpecTy::U32),
        SpecTy::U64 => Some(SpecTy::U64),
        SpecTy::Usize => Some(SpecTy::Usize),
        SpecTy::Seq(inner) => Some(SpecTy::Seq(Box::new(try_instantiate_spec_ty(
            inner, bindings,
        )?))),
        SpecTy::Tuple(items) => items
            .iter()
            .map(|item| try_instantiate_spec_ty(item, bindings))
            .collect::<Option<Vec<_>>>()
            .map(SpecTy::Tuple),
        SpecTy::Struct(struct_ty) => struct_ty
            .fields
            .iter()
            .map(|field| {
                Some(StructFieldTy {
                    name: field.name.clone(),
                    ty: try_instantiate_spec_ty(&field.ty, bindings)?,
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(|fields| {
                SpecTy::Struct(StructTy {
                    name: struct_ty.name.clone(),
                    fields,
                })
            }),
        SpecTy::Named { name, args } => args
            .iter()
            .map(|arg| try_instantiate_spec_ty(arg, bindings))
            .collect::<Option<Vec<_>>>()
            .map(|args| SpecTy::Named {
                name: name.clone(),
                args,
            }),
        SpecTy::TypeParam(name) => bindings.get(name).cloned(),
        SpecTy::Ref(inner) => Some(SpecTy::Ref(Box::new(try_instantiate_spec_ty(
            inner, bindings,
        )?))),
        SpecTy::Mut(inner) => Some(SpecTy::Mut(Box::new(try_instantiate_spec_ty(
            inner, bindings,
        )?))),
    }
}

fn infer_type_param_bindings(
    pattern: &SpecTy,
    actual: &SpecTy,
    bindings: &mut HashMap<String, SpecTy>,
) -> Result<(), String> {
    match pattern {
        SpecTy::TypeParam(name) => {
            if let Some(bound) = bindings.get(name) {
                let _ = unify_spec_tys(bound, actual)?;
            } else {
                bindings.insert(name.clone(), actual.clone());
            }
            Ok(())
        }
        SpecTy::Seq(inner) => match actual {
            SpecTy::Seq(actual_inner) => infer_type_param_bindings(inner, actual_inner, bindings),
            _ => {
                let _ = unify_spec_tys(pattern, actual)?;
                Ok(())
            }
        },
        SpecTy::Named { name, args } => match actual {
            SpecTy::Named {
                name: actual_name,
                args: actual_args,
            } if name == actual_name && args.len() == actual_args.len() => {
                for (arg, actual_arg) in args.iter().zip(actual_args) {
                    infer_type_param_bindings(arg, actual_arg, bindings)?;
                }
                Ok(())
            }
            _ => {
                let _ = unify_spec_tys(pattern, actual)?;
                Ok(())
            }
        },
        SpecTy::Tuple(items) => match actual {
            SpecTy::Tuple(actual_items) if items.len() == actual_items.len() => {
                for (item, actual_item) in items.iter().zip(actual_items) {
                    infer_type_param_bindings(item, actual_item, bindings)?;
                }
                Ok(())
            }
            _ => {
                let _ = unify_spec_tys(pattern, actual)?;
                Ok(())
            }
        },
        SpecTy::Struct(struct_ty) => match actual {
            SpecTy::Struct(actual_struct)
                if struct_ty.name == actual_struct.name
                    && struct_ty.fields.len() == actual_struct.fields.len() =>
            {
                for (field, actual_field) in struct_ty.fields.iter().zip(&actual_struct.fields) {
                    if field.name != actual_field.name {
                        return Err(format!(
                            "type mismatch between `{}` and `{}`",
                            display_spec_field_ty(field),
                            display_spec_field_ty(actual_field)
                        ));
                    }
                    infer_type_param_bindings(&field.ty, &actual_field.ty, bindings)?;
                }
                Ok(())
            }
            _ => {
                let _ = unify_spec_tys(pattern, actual)?;
                Ok(())
            }
        },
        SpecTy::Ref(inner) => match actual {
            SpecTy::Ref(actual_inner) => infer_type_param_bindings(inner, actual_inner, bindings),
            _ => {
                let _ = unify_spec_tys(pattern, actual)?;
                Ok(())
            }
        },
        SpecTy::Mut(inner) => match actual {
            SpecTy::Mut(actual_inner) => infer_type_param_bindings(inner, actual_inner, bindings),
            _ => {
                let _ = unify_spec_tys(pattern, actual)?;
                Ok(())
            }
        },
        _ => {
            let _ = unify_spec_tys(pattern, actual)?;
            Ok(())
        }
    }
}

fn seed_enum_type_param_bindings(
    enum_def: &EnumDef,
    expected: &SpecTy,
    bindings: &mut HashMap<String, SpecTy>,
) -> Result<bool, String> {
    let SpecTy::Named { name, args } = expected else {
        return Ok(false);
    };
    if *name != enum_def.name {
        return Ok(false);
    }
    if args.len() != enum_def.type_params.len() {
        return Err(format!(
            "constructor for `{}` expected {} type arguments, found {}",
            enum_def.name,
            enum_def.type_params.len(),
            args.len()
        ));
    }
    for (type_param, arg) in enum_def.type_params.iter().zip(args) {
        if let Some(bound) = bindings.get(type_param) {
            let _ = unify_spec_tys(bound, arg)?;
        } else {
            bindings.insert(type_param.clone(), arg.clone());
        }
    }
    Ok(true)
}

fn validate_enum_defs(
    enum_defs: &HashMap<String, EnumDef>,
    span: Span,
) -> Result<(), LoopPrepassError> {
    for enum_def in enum_defs.values() {
        let type_params: HashSet<_> = enum_def.type_params.iter().cloned().collect();
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
                validate_named_spec_ty(field_ty, enum_defs, &type_params).map_err(|message| {
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

fn is_empty_seq_lit(expr: &Expr) -> bool {
    matches!(expr, Expr::SeqLit(items) if items.is_empty())
}

fn known_spec_ty(ty: &InferredExprTy) -> Option<SpecTy> {
    match ty {
        InferredExprTy::Known(ty) => Some(ty.clone()),
        InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => None,
    }
}

fn infer_seq_lit_expr_types(
    items: &[Expr],
    expected: Option<&SpecTy>,
    infer_item: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<InferredExprTy, String>,
) -> Result<InferredExprTy, String> {
    let expected_item_ty = match expected {
        Some(SpecTy::Seq(inner)) => Some(inner.as_ref().clone()),
        Some(other) => {
            return Err(format!(
                "sequence literal requires `Seq<T>`, found `{}`",
                display_spec_ty(other)
            ));
        }
        None => None,
    };
    if items.is_empty() {
        return Ok(expected_item_ty
            .map(|inner| InferredExprTy::Known(SpecTy::Seq(Box::new(inner))))
            .unwrap_or(InferredExprTy::Unknown));
    }

    let mut item_ty = expected_item_ty;
    for item in items {
        let inferred_item = infer_item(item, item_ty.as_ref())?;
        if let Some(actual) = known_spec_ty(&inferred_item) {
            item_ty = Some(match &item_ty {
                Some(existing) => unify_spec_tys(existing, &actual)?,
                None => actual,
            });
        }
    }

    item_ty
        .map(|inner| InferredExprTy::Known(SpecTy::Seq(Box::new(inner))))
        .ok_or_else(|| "could not infer the element type of the sequence literal".to_owned())
}

fn type_seq_lit_expr(
    items: &[Expr],
    expected: Option<&SpecTy>,
    type_item: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    let expected_item_ty = match expected {
        Some(SpecTy::Seq(inner)) => Some(inner.as_ref().clone()),
        Some(other) => {
            return Err(format!(
                "sequence literal requires `Seq<T>`, found `{}`",
                display_spec_ty(other)
            ));
        }
        None => None,
    };

    let mut typed_items = Vec::with_capacity(items.len());
    let mut item_ty = expected_item_ty;
    for item in items {
        let typed_item = type_item(item, item_ty.as_ref())?;
        item_ty = Some(match &item_ty {
            Some(existing) => unify_spec_tys(existing, &typed_item.ty)?,
            None => typed_item.ty.clone(),
        });
        typed_items.push(typed_item);
    }

    let Some(item_ty) = item_ty else {
        return Err("empty sequence literal requires an expected `Seq<T>` type".to_owned());
    };
    Ok(TypedExpr {
        ty: SpecTy::Seq(Box::new(item_ty)),
        kind: TypedExprKind::SeqLit(typed_items),
    })
}

fn infer_seq_index_expr_types(
    base: &Expr,
    index: &Expr,
    infer_expr: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<InferredExprTy, String>,
) -> Result<InferredExprTy, String> {
    let base_ty = infer_expr(base, None)?;
    let index_ty = infer_expr(index, Some(&nat_spec_ty()))?;
    if let Some(index_ty) = known_spec_ty(&index_ty) {
        let unified = unify_spec_tys(&index_ty, &nat_spec_ty())?;
        if unified != nat_spec_ty() {
            return Err(format!(
                "sequence index requires `Nat`, found `{}`",
                display_spec_ty(&index_ty)
            ));
        }
    }
    match base_ty {
        InferredExprTy::Known(SpecTy::Seq(inner)) => Ok(InferredExprTy::Known(*inner)),
        InferredExprTy::Known(other) => Err(format!(
            "sequence indexing requires `Seq<T>`, found `{}`",
            display_spec_ty(&other)
        )),
        InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
    }
}

fn type_seq_index_expr(
    base: &Expr,
    index: &Expr,
    type_expr: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    let base = type_expr(base, None)?;
    let index = type_expr(index, Some(&nat_spec_ty()))?;
    if !is_nat_spec_ty(&index.ty) {
        return Err(format!(
            "sequence index requires `Nat`, found `{}`",
            display_spec_ty(&index.ty)
        ));
    }
    let SpecTy::Seq(item_ty) = &base.ty else {
        return Err(format!(
            "sequence indexing requires `Seq<T>`, found `{}`",
            display_spec_ty(&base.ty)
        ));
    };
    Ok(TypedExpr {
        ty: item_ty.as_ref().clone(),
        kind: TypedExprKind::Index {
            base: Box::new(base),
            index: Box::new(index),
        },
    })
}

fn infer_builtin_pure_call(
    func: &str,
    type_args: &[SpecTy],
    args: &[Expr],
    infer_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<InferredExprTy, String>,
) -> Result<Option<InferredExprTy>, String> {
    if !matches!(func, "seq_len" | "seq_rev") {
        return Ok(None);
    }
    if !type_args.is_empty() {
        return Err(format!(
            "type arguments are not supported on builtin pure function `{func}`"
        ));
    }
    if args.len() != 1 {
        return Err(format!(
            "builtin pure function `{func}` expects 1 argument, found {}",
            args.len()
        ));
    }
    let arg_ty = infer_arg(&args[0], None)?;
    let Some(arg_ty) = known_spec_ty(&arg_ty) else {
        return Ok(Some(InferredExprTy::Unknown));
    };
    let SpecTy::Seq(item_ty) = arg_ty else {
        return Err(format!(
            "builtin pure function `{func}` requires `Seq<T>`, found `{}`",
            display_spec_ty(&arg_ty)
        ));
    };
    Ok(Some(match func {
        "seq_len" => InferredExprTy::Known(nat_spec_ty()),
        "seq_rev" => InferredExprTy::Known(SpecTy::Seq(item_ty)),
        _ => unreachable!("checked builtin pure function"),
    }))
}

fn type_builtin_pure_call(
    func: &str,
    type_args: &[SpecTy],
    args: &[Expr],
    type_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<Option<TypedExpr>, String> {
    if !matches!(func, "seq_len" | "seq_rev") {
        return Ok(None);
    }
    if !type_args.is_empty() {
        return Err(format!(
            "type arguments are not supported on builtin pure function `{func}`"
        ));
    }
    if args.len() != 1 {
        return Err(format!(
            "builtin pure function `{func}` expects 1 argument, found {}",
            args.len()
        ));
    }
    let typed_arg = type_arg(&args[0], None)?;
    let SpecTy::Seq(item_ty) = &typed_arg.ty else {
        return Err(format!(
            "builtin pure function `{func}` requires `Seq<T>`, found `{}`",
            display_spec_ty(&typed_arg.ty)
        ));
    };
    Ok(Some(TypedExpr {
        ty: match func {
            "seq_len" => nat_spec_ty(),
            "seq_rev" => SpecTy::Seq(Box::new(item_ty.as_ref().clone())),
            _ => unreachable!("checked builtin pure function"),
        },
        kind: TypedExprKind::PureCall {
            func: func.to_owned(),
            args: vec![typed_arg],
        },
    }))
}

fn type_pure_call(
    func: &str,
    type_args: &[SpecTy],
    args: &[Expr],
    pure_fns: &HashMap<String, PureFnDef>,
    type_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    if let Some(typed) = type_builtin_pure_call(func, type_args, args, type_arg)? {
        return Ok(typed);
    }
    if !type_args.is_empty() {
        return Err(format!(
            "type arguments are only supported on enum constructors, found `{func}`"
        ));
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
        let typed_arg = type_arg(arg, Some(&param.ty))?;
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

fn explicit_enum_type_bindings(
    func: &str,
    enum_def: &EnumDef,
    type_args: &[SpecTy],
    enum_defs: &HashMap<String, EnumDef>,
) -> Result<HashMap<String, SpecTy>, String> {
    if type_args.is_empty() {
        return Ok(HashMap::new());
    }
    if enum_def.type_params.len() != type_args.len() {
        return Err(format!(
            "constructor `{func}` expects {} type arguments, found {}",
            enum_def.type_params.len(),
            type_args.len()
        ));
    }
    let scope = HashSet::new();
    for type_arg in type_args {
        validate_named_spec_ty(type_arg, enum_defs, &scope)?;
    }
    Ok(enum_def
        .type_params
        .iter()
        .cloned()
        .zip(type_args.iter().cloned())
        .collect())
}

fn instantiate_enum_result_ty(
    func: &str,
    enum_def: &EnumDef,
    bindings: &HashMap<String, SpecTy>,
) -> Result<SpecTy, String> {
    let mut type_args = Vec::with_capacity(enum_def.type_params.len());
    for type_param in &enum_def.type_params {
        let Some(arg) = bindings.get(type_param).cloned() else {
            return Err(format!(
                "could not infer type argument `{type_param}` for constructor `{func}`"
            ));
        };
        type_args.push(arg);
    }
    Ok(enum_result_ty(enum_def, type_args))
}

fn instantiate_named_ctor_field_tys(
    enum_def: &EnumDef,
    ctor_index: usize,
    type_args: &[SpecTy],
) -> Result<Vec<SpecTy>, String> {
    if enum_def.type_params.len() != type_args.len() {
        return Err(format!(
            "enum `{}` expects {} type arguments, found {}",
            enum_def.name,
            enum_def.type_params.len(),
            type_args.len()
        ));
    }
    let ctor = enum_def
        .ctors
        .get(ctor_index)
        .ok_or_else(|| format!("constructor index {ctor_index} out of range"))?;
    let bindings = enum_def
        .type_params
        .iter()
        .cloned()
        .zip(type_args.iter().cloned())
        .collect::<HashMap<_, _>>();
    ctor.fields
        .iter()
        .map(|field_ty| {
            try_instantiate_spec_ty(field_ty, &bindings).ok_or_else(|| {
                format!(
                    "could not instantiate field type for constructor `{}`",
                    ctor.name
                )
            })
        })
        .collect()
}

fn unsupported_match_expr_message() -> String {
    "match expressions are only supported in pure function bodies".to_owned()
}

fn typed_match_bindings(
    bindings: &[MatchBinding],
    field_tys: &[SpecTy],
    reserved_names: &HashSet<String>,
) -> Result<(Vec<TypedMatchBinding>, HashMap<String, SpecTy>), String> {
    if bindings.len() != field_tys.len() {
        return Err(format!(
            "match pattern expects {} bindings, found {}",
            field_tys.len(),
            bindings.len()
        ));
    }
    let mut seen = HashSet::new();
    let mut typed = Vec::with_capacity(bindings.len());
    let mut env = HashMap::new();
    for (binding, ty) in bindings.iter().zip(field_tys) {
        match binding {
            MatchBinding::Var(name) => {
                if reserved_names.contains(name) {
                    return Err(format!(
                        "match pattern binding `{name}` shadows an existing binding"
                    ));
                }
                if !seen.insert(name.clone()) {
                    return Err(format!("match pattern binds `{name}` more than once"));
                }
                env.insert(name.clone(), ty.clone());
                typed.push(TypedMatchBinding::Var {
                    name: name.clone(),
                    ty: ty.clone(),
                });
            }
            MatchBinding::Wildcard => typed.push(TypedMatchBinding::Wildcard { ty: ty.clone() }),
        }
    }
    Ok((typed, env))
}

fn merge_inferred_expr_tys(
    inferred: &mut SpecTypeInference,
    lhs: &InferredExprTy,
    rhs: &InferredExprTy,
) -> Result<InferredExprTy, String> {
    unify_expr_tys(inferred, lhs, rhs)?;
    Ok(match (lhs, rhs) {
        (InferredExprTy::Known(lhs), InferredExprTy::Known(rhs)) => {
            InferredExprTy::Known(unify_spec_tys(lhs, rhs)?)
        }
        (InferredExprTy::Known(ty), _) | (_, InferredExprTy::Known(ty)) => {
            InferredExprTy::Known(ty.clone())
        }
        (InferredExprTy::SpecVar(name), InferredExprTy::SpecVar(_))
        | (InferredExprTy::SpecVar(name), InferredExprTy::Unknown)
        | (InferredExprTy::Unknown, InferredExprTy::SpecVar(name)) => inferred
            .resolved_ty(name)
            .map(InferredExprTy::Known)
            .unwrap_or_else(|| InferredExprTy::SpecVar(name.clone())),
        (InferredExprTy::Unknown, InferredExprTy::Unknown) => InferredExprTy::Unknown,
    })
}

#[allow(clippy::too_many_arguments)]
fn infer_match_expr_types(
    scrutinee: &Expr,
    arms: &[crate::spec::MatchArm],
    default: Option<&Expr>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
) -> Result<InferredExprTy, String> {
    let scrutinee_ty = infer_contract_expr_types_with_expected(
        scrutinee,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        allow_bare_names,
        None,
    )?;
    let InferredExprTy::Known(SpecTy::Named {
        name: scrutinee_enum_name,
        args: scrutinee_type_args,
    }) = scrutinee_ty
    else {
        return Err("match scrutinee must have a named enum type".to_owned());
    };
    let enum_def = enum_defs
        .get(&scrutinee_enum_name)
        .ok_or_else(|| format!("unknown spec enum `{scrutinee_enum_name}`"))?;
    let mut reserved_names = params.keys().cloned().collect::<HashSet<_>>();
    reserved_names.extend(spec_scope.visible.iter().cloned());
    let mut seen_ctors = HashSet::new();
    let mut result_expr_ty = expected.cloned().map(InferredExprTy::Known);
    for arm in arms {
        let MatchPattern::Constructor {
            enum_name,
            ctor_name,
            bindings,
        } = &arm.pattern;
        if *enum_name != scrutinee_enum_name {
            return Err(format!(
                "match arm constructor `{enum_name}::{ctor_name}` does not match scrutinee type `{scrutinee_enum_name}`"
            ));
        }
        let Some(ctor_index) = enum_def
            .ctors
            .iter()
            .position(|ctor| ctor.name == *ctor_name)
        else {
            return Err(format!(
                "enum `{enum_name}` does not define constructor `{ctor_name}`"
            ));
        };
        if !seen_ctors.insert(ctor_index) {
            return Err(format!(
                "match expression contains duplicate arm for `{enum_name}::{ctor_name}`"
            ));
        }
        let field_tys =
            instantiate_named_ctor_field_tys(enum_def, ctor_index, &scrutinee_type_args)?;
        let (_typed_bindings, match_env) =
            typed_match_bindings(bindings, &field_tys, &reserved_names)?;
        let mut arm_params = params.clone();
        arm_params.extend(match_env);
        let mut arm_scope = spec_scope.clone();
        let arm_ty = infer_contract_expr_types_with_expected(
            &arm.body,
            pure_fns,
            enum_defs,
            &mut arm_scope,
            &arm_params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        )?;
        result_expr_ty = Some(if let Some(existing) = &result_expr_ty {
            merge_inferred_expr_tys(inferred, existing, &arm_ty)?
        } else {
            arm_ty
        });
    }
    if let Some(default) = default {
        let mut default_scope = spec_scope.clone();
        let default_ty = infer_contract_expr_types_with_expected(
            default,
            pure_fns,
            enum_defs,
            &mut default_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        )?;
        result_expr_ty = Some(if let Some(existing) = &result_expr_ty {
            merge_inferred_expr_tys(inferred, existing, &default_ty)?
        } else {
            default_ty
        });
    } else if seen_ctors.len() != enum_def.ctors.len() {
        return Err(format!(
            "match expression over `{scrutinee_enum_name}` is not exhaustive"
        ));
    }
    result_expr_ty.ok_or_else(|| "match expression must contain at least one arm".to_owned())
}

#[allow(clippy::too_many_arguments)]
fn typed_match_expr(
    scrutinee: &Expr,
    arms: &[crate::spec::MatchArm],
    default: Option<&Expr>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
) -> Result<TypedExpr, String> {
    let scrutinee = typed_contract_expr_with_expected(
        scrutinee,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        allow_bare_names,
        None,
    )?;
    let SpecTy::Named {
        name: scrutinee_enum_name,
        args: scrutinee_type_args,
    } = &scrutinee.ty
    else {
        return Err("match scrutinee must have a named enum type".to_owned());
    };
    let enum_def = enum_defs
        .get(scrutinee_enum_name)
        .ok_or_else(|| format!("unknown spec enum `{scrutinee_enum_name}`"))?;
    let mut reserved_names = params.keys().cloned().collect::<HashSet<_>>();
    reserved_names.extend(spec_scope.visible.iter().cloned());
    let mut seen_ctors = HashSet::new();
    let mut typed_arms = Vec::with_capacity(arms.len());
    let mut typed_default = None;
    let mut match_ty = expected.cloned();
    for arm in arms {
        let MatchPattern::Constructor {
            enum_name,
            ctor_name,
            bindings,
        } = &arm.pattern;
        if *enum_name != *scrutinee_enum_name {
            return Err(format!(
                "match arm constructor `{enum_name}::{ctor_name}` does not match scrutinee type `{scrutinee_enum_name}`"
            ));
        }
        let Some(ctor_index) = enum_def
            .ctors
            .iter()
            .position(|ctor| ctor.name == *ctor_name)
        else {
            return Err(format!(
                "enum `{enum_name}` does not define constructor `{ctor_name}`"
            ));
        };
        if !seen_ctors.insert(ctor_index) {
            return Err(format!(
                "match expression contains duplicate arm for `{enum_name}::{ctor_name}`"
            ));
        }
        let field_tys =
            instantiate_named_ctor_field_tys(enum_def, ctor_index, scrutinee_type_args)?;
        let (typed_bindings, match_env) =
            typed_match_bindings(bindings, &field_tys, &reserved_names)?;
        let mut arm_params = params.clone();
        arm_params.extend(match_env);
        let mut arm_scope = spec_scope.clone();
        let body = typed_contract_expr_with_expected(
            &arm.body,
            pure_fns,
            enum_defs,
            &mut arm_scope,
            &arm_params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        )?;
        match_ty = Some(if let Some(existing) = &match_ty {
            unify_spec_tys(existing, &body.ty)?
        } else {
            body.ty.clone()
        });
        typed_arms.push(TypedMatchArm {
            ctor_index,
            enum_name: enum_name.clone(),
            ctor_name: ctor_name.clone(),
            bindings: typed_bindings,
            body,
        });
    }
    if let Some(default) = default {
        let mut default_scope = spec_scope.clone();
        let body = typed_contract_expr_with_expected(
            default,
            pure_fns,
            enum_defs,
            &mut default_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        )?;
        match_ty = Some(if let Some(existing) = &match_ty {
            unify_spec_tys(existing, &body.ty)?
        } else {
            body.ty.clone()
        });
        typed_default = Some(Box::new(body));
    } else if seen_ctors.len() != enum_def.ctors.len() {
        return Err(format!(
            "match expression over `{scrutinee_enum_name}` is not exhaustive"
        ));
    }
    Ok(TypedExpr {
        ty: match_ty.ok_or_else(|| "match expression must contain at least one arm".to_owned())?,
        kind: TypedExprKind::Match {
            scrutinee: Box::new(scrutinee),
            arms: typed_arms,
            default: typed_default,
        },
    })
}

#[allow(clippy::too_many_arguments)]
fn infer_ctor_call_result_ty(
    func: &str,
    enum_def: &EnumDef,
    ctor_index: usize,
    type_args: &[SpecTy],
    args: &[Expr],
    enum_defs: &HashMap<String, EnumDef>,
    expected: Option<&SpecTy>,
    infer_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<InferredExprTy, String>,
) -> Result<SpecTy, String> {
    let ctor = &enum_def.ctors[ctor_index];
    if ctor.fields.len() != args.len() {
        return Err(format!(
            "constructor `{func}` expects {} arguments, found {}",
            ctor.fields.len(),
            args.len()
        ));
    }

    let mut bindings = explicit_enum_type_bindings(func, enum_def, type_args, enum_defs)?;
    if type_args.is_empty()
        && let Some(expected) = expected
    {
        let _ = seed_enum_type_param_bindings(enum_def, expected, &mut bindings)?;
    }

    for (arg, field_ty) in args.iter().zip(&ctor.fields) {
        let expected_field_ty = try_instantiate_spec_ty(field_ty, &bindings);
        let arg_ty = infer_arg(arg, expected_field_ty.as_ref())?;
        if let InferredExprTy::Known(actual_ty) = &arg_ty {
            infer_type_param_bindings(field_ty, actual_ty, &mut bindings)?;
        }
    }

    let result_ty = instantiate_enum_result_ty(func, enum_def, &bindings)?;
    if let Some(expected) = expected {
        let _ = unify_spec_tys(&result_ty, expected)?;
    }
    Ok(result_ty)
}

#[allow(clippy::too_many_arguments)]
fn type_ctor_call(
    func: &str,
    enum_def: &EnumDef,
    ctor_index: usize,
    type_args: &[SpecTy],
    args: &[Expr],
    enum_defs: &HashMap<String, EnumDef>,
    expected: Option<&SpecTy>,
    type_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    let ctor = &enum_def.ctors[ctor_index];
    if ctor.fields.len() != args.len() {
        return Err(format!(
            "constructor `{func}` expects {} arguments, found {}",
            ctor.fields.len(),
            args.len()
        ));
    }

    let mut bindings = explicit_enum_type_bindings(func, enum_def, type_args, enum_defs)?;
    if type_args.is_empty()
        && let Some(expected) = expected
    {
        let _ = seed_enum_type_param_bindings(enum_def, expected, &mut bindings)?;
    }

    let mut typed_args = Vec::with_capacity(args.len());
    for (arg, field_ty) in args.iter().zip(&ctor.fields) {
        let expected_field_ty = try_instantiate_spec_ty(field_ty, &bindings);
        let typed_arg = type_arg(arg, expected_field_ty.as_ref())?;
        if let Some(expected_field_ty) = &expected_field_ty {
            let _ = unify_spec_tys(&typed_arg.ty, expected_field_ty)?;
        }
        infer_type_param_bindings(field_ty, &typed_arg.ty, &mut bindings)?;
        typed_args.push(typed_arg);
    }

    let result_ty = instantiate_enum_result_ty(func, enum_def, &bindings)?;
    if let Some(expected) = expected {
        let _ = unify_spec_tys(&result_ty, expected)?;
    }
    Ok(TypedExpr {
        ty: result_ty,
        kind: TypedExprKind::CtorCall {
            enum_name: enum_def.name.clone(),
            ctor_name: ctor.name.clone(),
            ctor_index,
            args: typed_args,
        },
    })
}

#[allow(clippy::too_many_arguments)]
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
    infer_contract_expr_types_with_expected(
        expr,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        true,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn infer_runtime_contract_expr_types(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    infer_contract_expr_types_with_expected(
        expr,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn infer_contract_expr_types_with_expected(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(lit) => Ok(InferredExprTy::Known(lit.spec_ty())),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                inferred.ensure_var(name);
                if let Some(expected) = expected {
                    inferred.constrain(name, expected)?;
                }
                return Ok(InferredExprTy::SpecVar(name.clone()));
            }
            if allow_result && name == "result" {
                return Ok(InferredExprTy::Known(result_ty.clone()));
            }
            if allow_bare_names && let Some(ty) = params.get(name) {
                return Ok(InferredExprTy::Known(ty.clone()));
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::Interpolated(name) => {
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
        Expr::SeqLit(items) => infer_seq_lit_expr_types(items, expected, &mut |item, expected| {
            infer_contract_expr_types_with_expected(
                item,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::Match {
            scrutinee,
            arms,
            default,
        } => infer_match_expr_types(
            scrutinee,
            arms,
            default.as_deref(),
            pure_fns,
            enum_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        ),
        Expr::Bind(name) => {
            if allow_result && name == "result" {
                return Err("duplicate spec binding `?result` in //@ ens".to_owned());
            }
            spec_scope
                .bind(
                    name,
                    Span::default(),
                    None,
                    if allow_result { "ens" } else { "req" },
                )
                .map_err(|err| err.message)?;
            inferred.ensure_var(name);
            if let Some(expected) = expected {
                inferred.constrain(name, expected)?;
            }
            Ok(InferredExprTy::SpecVar(name.clone()))
        }
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                Ok(InferredExprTy::Known(infer_ctor_call_result_ty(
                    func,
                    enum_def,
                    ctor_index,
                    type_args,
                    args,
                    enum_defs,
                    expected,
                    &mut |arg, expected| {
                        infer_contract_expr_types_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            spec_scope,
                            params,
                            allow_result,
                            result_ty,
                            inferred,
                            allow_bare_names,
                            expected,
                        )
                    },
                )?))
            } else {
                if let Some(result) =
                    infer_builtin_pure_call(func, type_args, args, &mut |arg, expected| {
                        infer_contract_expr_types_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            spec_scope,
                            params,
                            allow_result,
                            result_ty,
                            inferred,
                            allow_bare_names,
                            expected,
                        )
                    })?
                {
                    return Ok(result);
                }
                if !type_args.is_empty() {
                    return Err(format!(
                        "type arguments are only supported on enum constructors, found `{func}`"
                    ));
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
                for (arg, param) in args.iter().zip(&def.params) {
                    let arg_ty = infer_contract_expr_types_with_expected(
                        arg,
                        pure_fns,
                        enum_defs,
                        spec_scope,
                        params,
                        allow_result,
                        result_ty,
                        inferred,
                        allow_bare_names,
                        Some(&param.ty),
                    )?;
                    constrain_expr_ty(inferred, &arg_ty, &param.ty)?;
                }
                Ok(InferredExprTy::Known(def.result_ty.clone()))
            }
        }
        Expr::Field { base, name } => {
            let base_ty = infer_contract_expr_types_with_expected(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            infer_named_field_expr_type(base_ty, name)
        }
        Expr::TupleField { base, .. } => {
            let base_ty = infer_contract_expr_types_with_expected(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            infer_tuple_field_expr_type(base_ty)
        }
        Expr::Index { base, index } => {
            infer_seq_index_expr_types(base, index, &mut |expr, expected| {
                infer_contract_expr_types_with_expected(
                    expr,
                    pure_fns,
                    enum_defs,
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                    allow_bare_names,
                    expected,
                )
            })
        }
        Expr::Deref { base } => {
            let base_ty = infer_contract_expr_types_with_expected(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
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
            let arg_ty = infer_contract_expr_types_with_expected(
                arg,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
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
            let lhs_ty = infer_contract_expr_types_with_expected(
                lhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            let rhs_expected = match (op, known_spec_ty(&lhs_ty)) {
                (
                    crate::spec::BinaryOp::Eq
                    | crate::spec::BinaryOp::Ne
                    | crate::spec::BinaryOp::Concat,
                    Some(ty),
                ) if is_empty_seq_lit(rhs) => Some(ty),
                _ => None,
            };
            let rhs_ty = infer_contract_expr_types_with_expected(
                rhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                rhs_expected.as_ref(),
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
                crate::spec::BinaryOp::Concat => {
                    let Some(lhs_ty) = known_spec_ty(&lhs_ty) else {
                        return Ok(InferredExprTy::Unknown);
                    };
                    let Some(rhs_ty) = known_spec_ty(&rhs_ty) else {
                        return Ok(InferredExprTy::Unknown);
                    };
                    let unified = unify_spec_tys(&lhs_ty, &rhs_ty)?;
                    if !matches!(unified, SpecTy::Seq(_)) {
                        return Err(format!(
                            "sequence concatenation requires `Seq<T>`, found `{}` and `{}`",
                            display_spec_ty(&lhs_ty),
                            display_spec_ty(&rhs_ty)
                        ));
                    }
                    Ok(InferredExprTy::Known(unified))
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
    infer_body_expr_types_with_expected(
        expr, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred, false, None,
    )
}

#[allow(clippy::too_many_arguments)]
fn infer_body_expr_types_with_expected(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(lit) => Ok(InferredExprTy::Known(lit.spec_ty())),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                inferred.ensure_var(name);
                if let Some(expected) = expected {
                    inferred.constrain(name, expected)?;
                }
                return Ok(InferredExprTy::SpecVar(name.clone()));
            }
            if allow_bare_names {
                return local_tys
                    .get(name)
                    .cloned()
                    .map(InferredExprTy::Known)
                    .ok_or_else(|| {
                        format!("unresolved binding `{name}` in //@ {}", kind.keyword())
                    });
            }
            Err(format!(
                "unresolved binding `{name}` in //@ {}",
                kind.keyword()
            ))
        }
        Expr::Interpolated(name) => local_tys
            .get(name)
            .cloned()
            .map(InferredExprTy::Known)
            .ok_or_else(|| format!("unresolved binding `{name}` in //@ {}", kind.keyword())),
        Expr::SeqLit(items) => infer_seq_lit_expr_types(items, expected, &mut |item, expected| {
            infer_body_expr_types_with_expected(
                item,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::Match { .. } => Err(unsupported_match_expr_message()),
        Expr::Bind(name) => {
            spec_scope
                .bind(name, Span::default(), None, kind.keyword())
                .map_err(|err| err.message)?;
            inferred.ensure_var(name);
            if let Some(expected) = expected {
                inferred.constrain(name, expected)?;
            }
            Ok(InferredExprTy::SpecVar(name.clone()))
        }
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                Ok(InferredExprTy::Known(infer_ctor_call_result_ty(
                    func,
                    enum_def,
                    ctor_index,
                    type_args,
                    args,
                    enum_defs,
                    expected,
                    &mut |arg, expected| {
                        infer_body_expr_types_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            kind,
                            spec_scope,
                            local_tys,
                            inferred,
                            allow_bare_names,
                            expected,
                        )
                    },
                )?))
            } else {
                if let Some(result) =
                    infer_builtin_pure_call(func, type_args, args, &mut |arg, expected| {
                        infer_body_expr_types_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            kind,
                            spec_scope,
                            local_tys,
                            inferred,
                            allow_bare_names,
                            expected,
                        )
                    })?
                {
                    return Ok(result);
                }
                if !type_args.is_empty() {
                    return Err(format!(
                        "type arguments are only supported on enum constructors, found `{func}`"
                    ));
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
                for (arg, param) in args.iter().zip(&def.params) {
                    let arg_ty = infer_body_expr_types_with_expected(
                        arg,
                        pure_fns,
                        enum_defs,
                        kind,
                        spec_scope,
                        local_tys,
                        inferred,
                        allow_bare_names,
                        Some(&param.ty),
                    )?;
                    constrain_expr_ty(inferred, &arg_ty, &param.ty)?;
                }
                Ok(InferredExprTy::Known(def.result_ty.clone()))
            }
        }
        Expr::Field { base, name } => {
            let base_ty = infer_body_expr_types_with_expected(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            infer_named_field_expr_type(base_ty, name)
        }
        Expr::TupleField { base, .. } => {
            let base_ty = infer_body_expr_types_with_expected(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            infer_tuple_field_expr_type(base_ty)
        }
        Expr::Index { base, index } => {
            infer_seq_index_expr_types(base, index, &mut |expr, expected| {
                infer_body_expr_types_with_expected(
                    expr,
                    pure_fns,
                    enum_defs,
                    kind,
                    spec_scope,
                    local_tys,
                    inferred,
                    allow_bare_names,
                    expected,
                )
            })
        }
        Expr::Deref { base } => {
            let base_ty = infer_body_expr_types_with_expected(
                base,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
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
            let arg_ty = infer_body_expr_types_with_expected(
                arg,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
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
            let lhs_ty = infer_body_expr_types_with_expected(
                lhs,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            let rhs_expected = match (op, known_spec_ty(&lhs_ty)) {
                (
                    crate::spec::BinaryOp::Eq
                    | crate::spec::BinaryOp::Ne
                    | crate::spec::BinaryOp::Concat,
                    Some(ty),
                ) if is_empty_seq_lit(rhs) => Some(ty),
                _ => None,
            };
            let rhs_ty = infer_body_expr_types_with_expected(
                rhs,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                rhs_expected.as_ref(),
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
                crate::spec::BinaryOp::Concat => {
                    let Some(lhs_ty) = known_spec_ty(&lhs_ty) else {
                        return Ok(InferredExprTy::Unknown);
                    };
                    let Some(rhs_ty) = known_spec_ty(&rhs_ty) else {
                        return Ok(InferredExprTy::Unknown);
                    };
                    let unified = unify_spec_tys(&lhs_ty, &rhs_ty)?;
                    if !matches!(unified, SpecTy::Seq(_)) {
                        return Err(format!(
                            "sequence concatenation requires `Seq<T>`, found `{}` and `{}`",
                            display_spec_ty(&lhs_ty),
                            display_spec_ty(&rhs_ty)
                        ));
                    }
                    Ok(InferredExprTy::Known(unified))
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

#[allow(clippy::too_many_arguments)]
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
    typed_contract_expr_with_expected(
        expr,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        true,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn typed_runtime_contract_expr(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<TypedExpr, String> {
    typed_contract_expr_with_expected(
        expr,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn typed_contract_expr_with_expected(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
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
            if allow_result && name == "result" {
                return Ok(TypedExpr {
                    ty: result_ty.clone(),
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            if allow_bare_names && let Some(ty) = params.get(name) {
                return Ok(TypedExpr {
                    ty: ty.clone(),
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::Interpolated(name) => {
            if allow_result && name == "result" {
                return Ok(TypedExpr {
                    ty: result_ty.clone(),
                    kind: TypedExprKind::Var(name.clone()),
                });
            }
            if let Some(ty) = params.get(name) {
                return Ok(TypedExpr {
                    ty: ty.clone(),
                    kind: TypedExprKind::RustVar(name.clone()),
                });
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::SeqLit(items) => type_seq_lit_expr(items, expected, &mut |item, expected| {
            typed_contract_expr_with_expected(
                item,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::Match {
            scrutinee,
            arms,
            default,
        } => typed_match_expr(
            scrutinee,
            arms,
            default.as_deref(),
            pure_fns,
            enum_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        ),
        Expr::Bind(name) => {
            if allow_result && name == "result" {
                return Err("duplicate spec binding `?result` in //@ ens".to_owned());
            }
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
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                type_ctor_call(
                    func,
                    enum_def,
                    ctor_index,
                    type_args,
                    args,
                    enum_defs,
                    expected,
                    &mut |arg, expected| {
                        typed_contract_expr_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            spec_scope,
                            params,
                            allow_result,
                            result_ty,
                            inferred,
                            allow_bare_names,
                            expected,
                        )
                    },
                )
            } else {
                type_pure_call(func, type_args, args, pure_fns, &mut |arg, expected| {
                    typed_contract_expr_with_expected(
                        arg,
                        pure_fns,
                        enum_defs,
                        spec_scope,
                        params,
                        allow_result,
                        result_ty,
                        inferred,
                        allow_bare_names,
                        expected,
                    )
                })
            }
        }
        Expr::Field { base, name } => {
            let base = typed_contract_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_named_field_expr(base, name)
        }
        Expr::TupleField { base, index } => {
            let base = typed_contract_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_tuple_field_expr(base, *index)
        }
        Expr::Index { base, index } => type_seq_index_expr(base, index, &mut |expr, expected| {
            typed_contract_expr_with_expected(
                expr,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::Deref { base } => {
            let base = typed_contract_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
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
            let arg = typed_contract_expr_with_expected(
                arg,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
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
            let lhs = typed_contract_expr_with_expected(
                lhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            let rhs_expected = match op {
                crate::spec::BinaryOp::Eq
                | crate::spec::BinaryOp::Ne
                | crate::spec::BinaryOp::Concat
                    if is_empty_seq_lit(rhs) =>
                {
                    Some(lhs.ty.clone())
                }
                _ => None,
            };
            let rhs = typed_contract_expr_with_expected(
                rhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                rhs_expected.as_ref(),
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
    typed_body_expr_with_expected(
        expr, pure_fns, enum_defs, kind, spec_scope, local_tys, inferred, false, None,
    )
}

#[allow(clippy::too_many_arguments)]
fn typed_body_expr_with_expected(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
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
            if !allow_bare_names {
                return Err(format!(
                    "unresolved binding `{name}` in //@ {}",
                    kind.keyword()
                ));
            }
            let ty = local_tys
                .get(name)
                .cloned()
                .ok_or_else(|| format!("unresolved binding `{name}` in //@ {}", kind.keyword()))?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::RustVar(name.clone()),
            })
        }
        Expr::Interpolated(name) => {
            let ty = local_tys
                .get(name)
                .cloned()
                .ok_or_else(|| format!("unresolved binding `{name}` in //@ {}", kind.keyword()))?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::RustVar(name.clone()),
            })
        }
        Expr::SeqLit(items) => type_seq_lit_expr(items, expected, &mut |item, expected| {
            typed_body_expr_with_expected(
                item,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::Match { .. } => Err(unsupported_match_expr_message()),
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
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                type_ctor_call(
                    func,
                    enum_def,
                    ctor_index,
                    type_args,
                    args,
                    enum_defs,
                    expected,
                    &mut |arg, expected| {
                        typed_body_expr_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            kind,
                            spec_scope,
                            local_tys,
                            inferred,
                            allow_bare_names,
                            expected,
                        )
                    },
                )
            } else {
                type_pure_call(func, type_args, args, pure_fns, &mut |arg, expected| {
                    typed_body_expr_with_expected(
                        arg,
                        pure_fns,
                        enum_defs,
                        kind,
                        spec_scope,
                        local_tys,
                        inferred,
                        allow_bare_names,
                        expected,
                    )
                })
            }
        }
        Expr::Field { base, name } => {
            let base = typed_body_expr_with_expected(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_named_field_expr(base, name)
        }
        Expr::TupleField { base, index } => {
            let base = typed_body_expr_with_expected(
                expr_base(base),
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_tuple_field_expr(base, *index)
        }
        Expr::Index { base, index } => type_seq_index_expr(base, index, &mut |expr, expected| {
            typed_body_expr_with_expected(
                expr,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::Deref { base } => {
            let base = typed_body_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
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
            let arg = typed_body_expr_with_expected(
                arg,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
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
            let lhs = typed_body_expr_with_expected(
                lhs,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            let rhs_expected = match op {
                crate::spec::BinaryOp::Eq
                | crate::spec::BinaryOp::Ne
                | crate::spec::BinaryOp::Concat
                    if is_empty_seq_lit(rhs) =>
                {
                    Some(lhs.ty.clone())
                }
                _ => None,
            };
            let rhs = typed_body_expr_with_expected(
                rhs,
                pure_fns,
                enum_defs,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                rhs_expected.as_ref(),
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
        crate::spec::BinaryOp::Concat => {
            let unified = unify_spec_tys(&lhs.ty, &rhs.ty)?;
            if !matches!(unified, SpecTy::Seq(_)) {
                return Err(format!(
                    "sequence concatenation requires `Seq<T>`, found `{}` and `{}`",
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

fn compute_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
    ghosts: &RawGlobalGhostPrepass,
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
        infer_runtime_contract_expr_types(
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
        infer_runtime_contract_expr_types(
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
            let typed = typed_runtime_contract_expr(
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
            Some(
                normalize_assert_like_predicate(typed, "//@ req").map_err(|message| {
                    LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message,
                    }
                })?,
            )
        }
        None => None,
    };
    let mut typed_body_assertions = HashMap::new();
    let mut typed_body_exprs = HashMap::new();
    let mut body_type_scope = if req_directive.is_some() {
        let mut scope = SpecScope::default();
        if let Some(directive) = req_directive {
            let _ = typed_runtime_contract_expr(
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
                let typed =
                    match directive.kind {
                        DirectiveKind::Assert => {
                            let predicate = normalize_assert_like_predicate(typed, "//@ assert")
                                .map_err(|message| LoopPrepassError {
                                    span: directive.span,
                                    display_span: Some(directive.span_text.clone()),
                                    message,
                                })?;
                            typed_body_assertions.insert(directive.span_text.clone(), predicate);
                            continue;
                        }
                        DirectiveKind::Assume => ensure_bind_free_predicate(typed, "//@ assume")
                            .map_err(|message| LoopPrepassError {
                                span: directive.span,
                                display_span: Some(directive.span_text.clone()),
                                message,
                            })?,
                        DirectiveKind::Inv => ensure_bind_free_predicate(typed, "//@ inv")
                            .map_err(|message| LoopPrepassError {
                                span: directive.span,
                                display_span: Some(directive.span_text.clone()),
                                message,
                            })?,
                        DirectiveKind::Req | DirectiveKind::Ens | DirectiveKind::LemmaCall => {
                            unreachable!("filtered above")
                        }
                    };
                typed_body_exprs.insert(directive.span_text.clone(), typed);
            }
        }
    }
    let typed_ens = match ens_directive {
        Some(directive) => {
            let mut scope = SpecScope::default();
            if let Some(req) = req_directive {
                let _ = typed_runtime_contract_expr(
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
            let typed = typed_runtime_contract_expr(
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
            })?;
            Some(
                ensure_bind_free_predicate(typed, "//@ ens").map_err(|message| {
                    LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message,
                    }
                })?,
            )
        }
        None => None,
    };
    let function_contract = match (req_directive, ens_directive) {
        (None, None) => Some(FunctionContract {
            params: params.clone(),
            req: NormalizedPredicate {
                bindings: Vec::new(),
                condition: typed_bool_expr(true),
            },
            req_span: def_span.clone(),
            ens: typed_bool_expr(true),
            ens_span: def_span,
            result,
        }),
        (Some(req), Some(ens)) => Some(FunctionContract {
            params: params.clone(),
            req: typed_req.expect("typed req"),
            req_span: req.span_text.clone(),
            ens: typed_ens.expect("typed ens"),
            ens_span: ens.span_text.clone(),
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
    let mut control_point_directives = ControlPointDirectives::default();

    for directive in directives.directives {
        match directive.kind {
            DirectiveKind::Req | DirectiveKind::Ens => {}
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
                        assertion: typed_body_assertions
                            .get(&directive.span_text)
                            .cloned()
                            .expect("typed assertion expression"),
                        resolution,
                        assertion_span: directive.span_text.clone(),
                    }));
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
            }
            DirectiveKind::Inv => {}
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
            }
        }
    }

    Ok(DirectivePrepass {
        loop_contracts,
        control_point_directives,
        function_contract,
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
    let (lemma_name, _, args) = lemma_call_parts(expr).map_err(|message| LoopPrepassError {
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
    let (lemma_name, type_args, args) = lemma_call_parts(expr)?;
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
    let type_param_scope = HashSet::new();
    let mut bindings = seed_lemma_type_bindings(
        lemma_name,
        &lemma.type_params,
        type_args,
        enum_defs,
        &type_param_scope,
    )?;
    let mut arg_tys = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&lemma.params) {
        let expected = try_instantiate_spec_ty(&param.ty, &bindings);
        let arg_ty = infer_body_expr_types_with_expected(
            arg,
            pure_fns,
            enum_defs,
            DirectiveKind::LemmaCall,
            spec_scope,
            local_tys,
            inferred,
            false,
            expected.as_ref(),
        )?;
        if let Some(actual) = known_spec_ty(&arg_ty) {
            infer_type_param_bindings(&param.ty, &actual, &mut bindings)?;
        }
        arg_tys.push(arg_ty);
    }
    if lemma
        .type_params
        .iter()
        .all(|type_param| bindings.contains_key(type_param))
    {
        let param_tys = instantiate_lemma_param_tys(lemma_name, lemma, &bindings)?;
        for (arg_ty, param_ty) in arg_tys.iter().zip(param_tys.iter()) {
            constrain_expr_ty(inferred, arg_ty, param_ty)?;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
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
    let (lemma_name, type_args, args) = lemma_call_parts(expr)?;
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
    let type_param_scope = HashSet::new();
    let mut bindings = seed_lemma_type_bindings(
        lemma_name,
        &lemma.type_params,
        type_args,
        enum_defs,
        &type_param_scope,
    )?;
    let mut typed_args = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&lemma.params) {
        let expected = try_instantiate_spec_ty(&param.ty, &bindings);
        let typed = typed_body_expr_with_expected(
            arg,
            pure_fns,
            enum_defs,
            DirectiveKind::LemmaCall,
            spec_scope,
            local_tys,
            inferred,
            false,
            expected.as_ref(),
        )?;
        infer_type_param_bindings(&param.ty, &typed.ty, &mut bindings)?;
        typed_args.push(typed);
    }
    let param_tys = instantiate_lemma_param_tys(lemma_name, lemma, &bindings)?;
    for ((typed_arg, param), param_ty) in typed_args
        .iter()
        .zip(lemma.params.iter())
        .zip(param_tys.iter())
    {
        let unified = unify_spec_tys(&typed_arg.ty, param_ty)?;
        if unified != *param_ty {
            return Err(format!(
                "lemma `{lemma_name}` parameter `{}` expects `{}`, found `{}`",
                param.name,
                display_spec_ty(param_ty),
                display_spec_ty(&typed_arg.ty)
            ));
        }
    }
    Ok(LemmaCallContract {
        lemma_name: lemma_name.to_owned(),
        args: typed_args,
        resolution: ResolvedExprEnv::default(),
        span_text: span_text.to_owned(),
    })
}

fn typed_expr_calls_pure_fn(expr: &TypedExpr, name: &str) -> bool {
    match &expr.kind {
        TypedExprKind::PureCall { func, args } => {
            func == name || args.iter().any(|arg| typed_expr_calls_pure_fn(arg, name))
        }
        TypedExprKind::SeqLit(items) => items
            .iter()
            .any(|item| typed_expr_calls_pure_fn(item, name)),
        TypedExprKind::Match {
            scrutinee,
            arms,
            default,
        } => {
            typed_expr_calls_pure_fn(scrutinee, name)
                || arms
                    .iter()
                    .any(|arm| typed_expr_calls_pure_fn(&arm.body, name))
                || default
                    .as_deref()
                    .is_some_and(|body| typed_expr_calls_pure_fn(body, name))
        }
        TypedExprKind::CtorCall { args, .. } => {
            args.iter().any(|arg| typed_expr_calls_pure_fn(arg, name))
        }
        TypedExprKind::Field { base, .. }
        | TypedExprKind::TupleField { base, .. }
        | TypedExprKind::Deref { base }
        | TypedExprKind::Fin { base }
        | TypedExprKind::Unary { arg: base, .. } => typed_expr_calls_pure_fn(base, name),
        TypedExprKind::Index { base, index } => {
            typed_expr_calls_pure_fn(base, name) || typed_expr_calls_pure_fn(index, name)
        }
        TypedExprKind::Binary { lhs, rhs, .. } => {
            typed_expr_calls_pure_fn(lhs, name) || typed_expr_calls_pure_fn(rhs, name)
        }
        TypedExprKind::Bool(_)
        | TypedExprKind::Int(_)
        | TypedExprKind::Var(_)
        | TypedExprKind::RustVar(_)
        | TypedExprKind::Bind(_) => false,
    }
}

struct RecursivePureFnContext<'a> {
    function_name: &'a str,
    recursive_param_index: usize,
    recursive_param_name: &'a str,
    recursive_param_ty: &'a SpecTy,
}

fn validate_recursive_pure_expr(
    expr: &TypedExpr,
    ctx: &RecursivePureFnContext<'_>,
    allowed_recursive_vars: &HashSet<String>,
) -> Result<(), String> {
    match &expr.kind {
        TypedExprKind::PureCall { func, args } => {
            if func == ctx.function_name {
                let Some(recursion_arg) = args.get(ctx.recursive_param_index) else {
                    return Err(format!(
                        "recursive call to `{}` has the wrong arity",
                        ctx.function_name
                    ));
                };
                match &recursion_arg.kind {
                    TypedExprKind::Var(name) if allowed_recursive_vars.contains(name) => {}
                    _ => {
                        return Err(format!(
                            "recursive call to `{}` must pass a pattern-bound subcomponent as parameter `{}`",
                            ctx.function_name, ctx.recursive_param_name
                        ));
                    }
                }
            }
            for arg in args {
                validate_recursive_pure_expr(arg, ctx, allowed_recursive_vars)?;
            }
            Ok(())
        }
        TypedExprKind::Match {
            scrutinee,
            arms,
            default,
        } => {
            validate_recursive_pure_expr(scrutinee, ctx, allowed_recursive_vars)?;
            let allows_descent = matches!(
                &scrutinee.kind,
                TypedExprKind::Var(name)
                    if (name == ctx.recursive_param_name || allowed_recursive_vars.contains(name))
                        && scrutinee.ty == *ctx.recursive_param_ty
            );
            for arm in arms {
                let mut arm_allowed = allowed_recursive_vars.clone();
                if allows_descent {
                    for binding in &arm.bindings {
                        if let TypedMatchBinding::Var { name, ty } = binding
                            && *ty == *ctx.recursive_param_ty
                        {
                            arm_allowed.insert(name.clone());
                        }
                    }
                }
                validate_recursive_pure_expr(&arm.body, ctx, &arm_allowed)?;
            }
            if let Some(default) = default {
                validate_recursive_pure_expr(default, ctx, allowed_recursive_vars)?;
            }
            Ok(())
        }
        TypedExprKind::CtorCall { args, .. } => {
            for arg in args {
                validate_recursive_pure_expr(arg, ctx, allowed_recursive_vars)?;
            }
            Ok(())
        }
        TypedExprKind::SeqLit(items) => {
            for item in items {
                validate_recursive_pure_expr(item, ctx, allowed_recursive_vars)?;
            }
            Ok(())
        }
        TypedExprKind::Field { base, .. }
        | TypedExprKind::TupleField { base, .. }
        | TypedExprKind::Deref { base }
        | TypedExprKind::Fin { base }
        | TypedExprKind::Unary { arg: base, .. } => {
            validate_recursive_pure_expr(base, ctx, allowed_recursive_vars)
        }
        TypedExprKind::Index { base, index } => {
            validate_recursive_pure_expr(base, ctx, allowed_recursive_vars)?;
            validate_recursive_pure_expr(index, ctx, allowed_recursive_vars)
        }
        TypedExprKind::Binary { lhs, rhs, .. } => {
            validate_recursive_pure_expr(lhs, ctx, allowed_recursive_vars)?;
            validate_recursive_pure_expr(rhs, ctx, allowed_recursive_vars)
        }
        TypedExprKind::Bool(_)
        | TypedExprKind::Int(_)
        | TypedExprKind::Var(_)
        | TypedExprKind::RustVar(_)
        | TypedExprKind::Bind(_) => Ok(()),
    }
}

fn validate_recursive_pure_fn(def: &TypedPureFnDef) -> Result<(), String> {
    if !typed_expr_calls_pure_fn(&def.body, &def.name) {
        return Ok(());
    }
    let TypedExprKind::Match {
        scrutinee,
        arms,
        default,
    } = &def.body.kind
    else {
        return Err("recursive pure functions must use `match` at the top level".to_owned());
    };
    let TypedExprKind::Var(scrutinee_name) = &scrutinee.kind else {
        return Err("recursive pure functions must match on a parameter variable".to_owned());
    };
    let Some(recursive_param_index) = def
        .params
        .iter()
        .position(|param| param.name == *scrutinee_name)
    else {
        return Err("recursive pure functions must match on one of their parameters".to_owned());
    };
    let recursive_param = &def.params[recursive_param_index];
    if !matches!(recursive_param.ty, SpecTy::Named { .. }) {
        return Err("recursive pure functions require a named enum parameter".to_owned());
    }
    let ctx = RecursivePureFnContext {
        function_name: &def.name,
        recursive_param_index,
        recursive_param_name: &recursive_param.name,
        recursive_param_ty: &recursive_param.ty,
    };
    for arm in arms {
        let mut allowed_recursive_vars = HashSet::new();
        for binding in &arm.bindings {
            if let TypedMatchBinding::Var { name, ty } = binding
                && *ty == recursive_param.ty
            {
                allowed_recursive_vars.insert(name.clone());
            }
        }
        validate_recursive_pure_expr(&arm.body, &ctx, &allowed_recursive_vars)?;
    }
    if let Some(default) = default {
        validate_recursive_pure_expr(default, &ctx, &HashSet::new())?;
    }
    Ok(())
}

fn type_pure_fns(
    pure_fns: &HashMap<String, PureFnDef>,
    declaration_order: &[String],
    enum_defs: &HashMap<String, EnumDef>,
    span: Span,
) -> Result<Vec<TypedPureFnDef>, LoopPrepassError> {
    let mut available_pure_fns = HashMap::new();
    let mut typed = Vec::with_capacity(declaration_order.len());
    for name in declaration_order {
        let def = pure_fns
            .get(name)
            .expect("pure function declaration order must stay in sync");
        available_pure_fns.insert(def.name.clone(), def.clone());
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
            &available_pure_fns,
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
            &available_pure_fns,
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
        let typed_def = TypedPureFnDef {
            name: def.name.clone(),
            params,
            body,
        };
        validate_recursive_pure_fn(&typed_def).map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("pure function `{}` body: {message}", def.name),
        })?;
        typed.push(typed_def);
    }
    Ok(typed)
}

fn lemma_body_callee<'a>(
    name: &str,
    available_lemmas: &'a HashMap<String, LemmaDef>,
    all_lemmas: &HashMap<String, LemmaDef>,
) -> Result<&'a LemmaDef, String> {
    if let Some(lemma) = available_lemmas.get(name) {
        return Ok(lemma);
    }
    if all_lemmas.contains_key(name) {
        return Err("A lemma can call only preceding lemmas or itself.".to_owned());
    }
    Err(format!("unknown lemma `{name}`"))
}

#[allow(clippy::too_many_arguments)]
fn infer_lemma_stmts(
    stmts: &[crate::spec::GhostStmt],
    available_lemmas: &HashMap<String, LemmaDef>,
    all_lemmas: &HashMap<String, LemmaDef>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            crate::spec::GhostStmt::Assert(expr) | crate::spec::GhostStmt::Assume(expr) => {
                infer_contract_expr_types(
                    expr, pure_fns, enum_defs, spec_scope, local_tys, false, result_ty, inferred,
                )?;
            }
            crate::spec::GhostStmt::Call {
                name,
                type_args,
                args,
            } => {
                let callee = lemma_body_callee(name, available_lemmas, all_lemmas)?;
                if callee.params.len() != args.len() {
                    return Err(format!(
                        "lemma `{name}` expects {} arguments, found {}",
                        callee.params.len(),
                        args.len()
                    ));
                }
                let mut bindings = seed_lemma_type_bindings(
                    name,
                    &callee.type_params,
                    type_args,
                    enum_defs,
                    type_param_scope,
                )?;
                let mut arg_tys = Vec::with_capacity(args.len());
                for (arg, param) in args.iter().zip(&callee.params) {
                    let expected = try_instantiate_spec_ty(&param.ty, &bindings);
                    let arg_ty = infer_contract_expr_types_with_expected(
                        arg,
                        pure_fns,
                        enum_defs,
                        spec_scope,
                        local_tys,
                        false,
                        result_ty,
                        inferred,
                        true,
                        expected.as_ref(),
                    )?;
                    if let Some(actual) = known_spec_ty(&arg_ty) {
                        infer_type_param_bindings(&param.ty, &actual, &mut bindings)?;
                    }
                    arg_tys.push(arg_ty);
                }
                if callee
                    .type_params
                    .iter()
                    .all(|type_param| bindings.contains_key(type_param))
                {
                    let param_tys = instantiate_lemma_param_tys(name, callee, &bindings)?;
                    for (arg_ty, param_ty) in arg_tys.iter().zip(param_tys.iter()) {
                        constrain_expr_ty(inferred, arg_ty, param_ty)?;
                    }
                }
            }
            crate::spec::GhostStmt::Match {
                scrutinee,
                arms,
                default,
            } => {
                let scrutinee_ty = infer_contract_expr_types(
                    scrutinee, pure_fns, enum_defs, spec_scope, local_tys, false, result_ty,
                    inferred,
                )?;
                let InferredExprTy::Known(SpecTy::Named {
                    name: scrutinee_enum_name,
                    args: scrutinee_type_args,
                }) = scrutinee_ty
                else {
                    return Err("match scrutinee must have a named enum type".to_owned());
                };
                let enum_def = enum_defs
                    .get(&scrutinee_enum_name)
                    .ok_or_else(|| format!("unknown spec enum `{scrutinee_enum_name}`"))?;
                let mut reserved_names = local_tys.keys().cloned().collect::<HashSet<_>>();
                reserved_names.extend(spec_scope.visible.iter().cloned());
                let mut seen_ctors = HashSet::new();
                for arm in arms {
                    let GhostMatchArm { pattern, body } = arm;
                    let MatchPattern::Constructor {
                        enum_name,
                        ctor_name,
                        bindings,
                    } = pattern;
                    if *enum_name != scrutinee_enum_name {
                        return Err(format!(
                            "match arm constructor `{enum_name}::{ctor_name}` does not match scrutinee type `{scrutinee_enum_name}`"
                        ));
                    }
                    let Some(ctor_index) = enum_def
                        .ctors
                        .iter()
                        .position(|ctor| ctor.name == *ctor_name)
                    else {
                        return Err(format!(
                            "enum `{enum_name}` does not define constructor `{ctor_name}`"
                        ));
                    };
                    if !seen_ctors.insert(ctor_index) {
                        return Err(format!(
                            "match statement contains duplicate arm for `{enum_name}::{ctor_name}`"
                        ));
                    }
                    let field_tys = instantiate_named_ctor_field_tys(
                        enum_def,
                        ctor_index,
                        &scrutinee_type_args,
                    )?;
                    let (_typed_bindings, match_env) =
                        typed_match_bindings(bindings, &field_tys, &reserved_names)?;
                    let mut arm_tys = local_tys.clone();
                    arm_tys.extend(match_env);
                    let mut arm_scope = spec_scope.clone();
                    infer_lemma_stmts(
                        body,
                        available_lemmas,
                        all_lemmas,
                        pure_fns,
                        enum_defs,
                        type_param_scope,
                        &mut arm_scope,
                        &arm_tys,
                        result_ty,
                        inferred,
                    )?;
                }
                if let Some(default) = default {
                    let mut default_scope = spec_scope.clone();
                    infer_lemma_stmts(
                        default,
                        available_lemmas,
                        all_lemmas,
                        pure_fns,
                        enum_defs,
                        type_param_scope,
                        &mut default_scope,
                        local_tys,
                        result_ty,
                        inferred,
                    )?;
                } else if seen_ctors.len() != enum_def.ctors.len() {
                    return Err(format!(
                        "match statement over `{scrutinee_enum_name}` is not exhaustive"
                    ));
                }
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn typed_lemma_stmts(
    stmts: &[crate::spec::GhostStmt],
    available_lemmas: &HashMap<String, LemmaDef>,
    all_lemmas: &HashMap<String, LemmaDef>,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<Vec<TypedGhostStmt>, String> {
    let mut typed = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        match stmt {
            crate::spec::GhostStmt::Assert(expr) => {
                let typed_expr = typed_contract_expr(
                    expr, pure_fns, enum_defs, spec_scope, local_tys, false, result_ty, inferred,
                )?;
                typed.push(TypedGhostStmt::Assert(normalize_assert_like_predicate(
                    typed_expr,
                    "ghost assert",
                )?))
            }
            crate::spec::GhostStmt::Assume(expr) => {
                let typed_expr = typed_contract_expr(
                    expr, pure_fns, enum_defs, spec_scope, local_tys, false, result_ty, inferred,
                )?;
                typed.push(TypedGhostStmt::Assume(ensure_bind_free_predicate(
                    typed_expr,
                    "ghost assume",
                )?))
            }
            crate::spec::GhostStmt::Call {
                name,
                type_args,
                args,
            } => {
                let callee = lemma_body_callee(name, available_lemmas, all_lemmas)?;
                if callee.params.len() != args.len() {
                    return Err(format!(
                        "lemma `{name}` expects {} arguments, found {}",
                        callee.params.len(),
                        args.len()
                    ));
                }
                let mut bindings = seed_lemma_type_bindings(
                    name,
                    &callee.type_params,
                    type_args,
                    enum_defs,
                    type_param_scope,
                )?;
                let mut typed_args = Vec::with_capacity(args.len());
                for (arg, param) in args.iter().zip(&callee.params) {
                    let expected = try_instantiate_spec_ty(&param.ty, &bindings);
                    let typed_arg = typed_contract_expr_with_expected(
                        arg,
                        pure_fns,
                        enum_defs,
                        spec_scope,
                        local_tys,
                        false,
                        result_ty,
                        inferred,
                        true,
                        expected.as_ref(),
                    )?;
                    infer_type_param_bindings(&param.ty, &typed_arg.ty, &mut bindings)?;
                    typed_args.push(typed_arg);
                }
                let param_tys = instantiate_lemma_param_tys(name, callee, &bindings)?;
                for ((typed_arg, param), param_ty) in typed_args
                    .iter()
                    .zip(callee.params.iter())
                    .zip(param_tys.iter())
                {
                    let unified = unify_spec_tys(&typed_arg.ty, param_ty)?;
                    if unified != *param_ty {
                        return Err(format!(
                            "lemma `{name}` parameter `{}` expects `{}`, found `{}`",
                            param.name,
                            display_spec_ty(param_ty),
                            display_spec_ty(&typed_arg.ty)
                        ));
                    }
                }
                typed.push(TypedGhostStmt::Call {
                    lemma_name: name.clone(),
                    args: typed_args,
                });
            }
            crate::spec::GhostStmt::Match {
                scrutinee,
                arms,
                default,
            } => {
                let scrutinee = typed_contract_expr(
                    scrutinee, pure_fns, enum_defs, spec_scope, local_tys, false, result_ty,
                    inferred,
                )?;
                let SpecTy::Named {
                    name: scrutinee_enum_name,
                    args: scrutinee_type_args,
                } = &scrutinee.ty
                else {
                    return Err("match scrutinee must have a named enum type".to_owned());
                };
                let enum_def = enum_defs
                    .get(scrutinee_enum_name)
                    .ok_or_else(|| format!("unknown spec enum `{scrutinee_enum_name}`"))?;
                let mut reserved_names = local_tys.keys().cloned().collect::<HashSet<_>>();
                reserved_names.extend(spec_scope.visible.iter().cloned());
                let mut seen_ctors = HashSet::new();
                let mut typed_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let GhostMatchArm { pattern, body } = arm;
                    let MatchPattern::Constructor {
                        enum_name,
                        ctor_name,
                        bindings,
                    } = pattern;
                    if *enum_name != *scrutinee_enum_name {
                        return Err(format!(
                            "match arm constructor `{enum_name}::{ctor_name}` does not match scrutinee type `{scrutinee_enum_name}`"
                        ));
                    }
                    let Some(ctor_index) = enum_def
                        .ctors
                        .iter()
                        .position(|ctor| ctor.name == *ctor_name)
                    else {
                        return Err(format!(
                            "enum `{enum_name}` does not define constructor `{ctor_name}`"
                        ));
                    };
                    if !seen_ctors.insert(ctor_index) {
                        return Err(format!(
                            "match statement contains duplicate arm for `{enum_name}::{ctor_name}`"
                        ));
                    }
                    let field_tys = instantiate_named_ctor_field_tys(
                        enum_def,
                        ctor_index,
                        scrutinee_type_args,
                    )?;
                    let (typed_bindings, match_env) =
                        typed_match_bindings(bindings, &field_tys, &reserved_names)?;
                    let mut arm_tys = local_tys.clone();
                    arm_tys.extend(match_env);
                    let mut arm_scope = spec_scope.clone();
                    let body = typed_lemma_stmts(
                        body,
                        available_lemmas,
                        all_lemmas,
                        pure_fns,
                        enum_defs,
                        type_param_scope,
                        &mut arm_scope,
                        &arm_tys,
                        result_ty,
                        inferred,
                    )?;
                    typed_arms.push(TypedGhostMatchArm {
                        ctor_index,
                        bindings: typed_bindings,
                        body,
                    });
                }
                let typed_default = if let Some(default) = default {
                    let mut default_scope = spec_scope.clone();
                    Some(typed_lemma_stmts(
                        default,
                        available_lemmas,
                        all_lemmas,
                        pure_fns,
                        enum_defs,
                        type_param_scope,
                        &mut default_scope,
                        local_tys,
                        result_ty,
                        inferred,
                    )?)
                } else {
                    None
                };
                if typed_default.is_none() && seen_ctors.len() != enum_def.ctors.len() {
                    return Err(format!(
                        "match statement over `{scrutinee_enum_name}` is not exhaustive"
                    ));
                }
                typed.push(TypedGhostStmt::Match {
                    scrutinee,
                    arms: typed_arms,
                    default: typed_default,
                });
            }
        }
    }
    Ok(typed)
}

fn typed_ghost_stmts_call_lemma(stmts: &[TypedGhostStmt], name: &str) -> bool {
    stmts.iter().any(|stmt| match stmt {
        TypedGhostStmt::Call { lemma_name, .. } => lemma_name == name,
        TypedGhostStmt::Match { arms, default, .. } => {
            arms.iter()
                .any(|arm| typed_ghost_stmts_call_lemma(&arm.body, name))
                || default
                    .as_deref()
                    .is_some_and(|body| typed_ghost_stmts_call_lemma(body, name))
        }
        TypedGhostStmt::Assert(_) | TypedGhostStmt::Assume(_) => false,
    })
}

struct RecursiveLemmaContext<'a> {
    lemma_name: &'a str,
    induction_param_index: usize,
    params: &'a [ContractParam],
}

fn recursive_lemma_measure(
    arg: &TypedExpr,
    param: &ContractParam,
    size_map: &HashMap<String, (String, i32)>,
) -> Option<i32> {
    match &arg.kind {
        TypedExprKind::Var(name) if name == &param.name => Some(0),
        TypedExprKind::Var(name) => size_map
            .get(name)
            .and_then(|(root, depth)| (root == &param.name).then_some(*depth)),
        TypedExprKind::RustVar(_) => None,
        _ => None,
    }
}

fn validate_recursive_lemma_stmts(
    stmts: &[TypedGhostStmt],
    ctx: &RecursiveLemmaContext<'_>,
    size_map: &HashMap<String, (String, i32)>,
) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            TypedGhostStmt::Assert(_) | TypedGhostStmt::Assume(_) => {}
            TypedGhostStmt::Call { lemma_name, args } => {
                if lemma_name != ctx.lemma_name {
                    continue;
                }
                if ctx.induction_param_index == 0 {
                    let mut found_smaller = false;
                    for (param, arg) in ctx.params.iter().zip(args.iter()) {
                        match recursive_lemma_measure(arg, param, size_map) {
                            Some(depth) if depth < 0 => {
                                found_smaller = true;
                                break;
                            }
                            Some(0) => {}
                            _ => return Err(
                                "recursive lemma call does not decrease the inductive parameter(s)"
                                    .to_owned(),
                            ),
                        }
                    }
                    if !found_smaller {
                        return Err(
                            "recursive lemma call does not decrease the inductive parameter(s)"
                                .to_owned(),
                        );
                    }
                } else {
                    let param = &ctx.params[ctx.induction_param_index];
                    if !matches!(
                        args.get(ctx.induction_param_index)
                            .and_then(|arg| recursive_lemma_measure(arg, param, size_map)),
                        Some(depth) if depth < 0
                    ) {
                        return Err(
                            "recursive lemma call does not decrease the inductive parameter(s)"
                                .to_owned(),
                        );
                    }
                }
            }
            TypedGhostStmt::Match {
                scrutinee,
                arms,
                default,
            } => {
                let branch_root = match &scrutinee.kind {
                    TypedExprKind::Var(name) => size_map.get(name).cloned(),
                    TypedExprKind::RustVar(_) => None,
                    _ => None,
                };
                for arm in arms {
                    let mut arm_size_map = size_map.clone();
                    if let Some((root, depth)) = &branch_root {
                        for binding in &arm.bindings {
                            if let TypedMatchBinding::Var { name, .. } = binding {
                                arm_size_map.insert(name.clone(), (root.clone(), depth - 1));
                            }
                        }
                    }
                    validate_recursive_lemma_stmts(&arm.body, ctx, &arm_size_map)?;
                }
                if let Some(default) = default {
                    validate_recursive_lemma_stmts(default, ctx, size_map)?;
                }
            }
        }
    }
    Ok(())
}

fn validate_recursive_lemma(def: &TypedLemmaDef) -> Result<(), String> {
    if !typed_ghost_stmts_call_lemma(&def.body, &def.name) {
        return Ok(());
    }
    let [TypedGhostStmt::Match { scrutinee, .. }] = def.body.as_slice() else {
        return Err("recursive lemmas must use `match` as the only top-level statement".to_owned());
    };
    let TypedExprKind::Var(scrutinee_name) = &scrutinee.kind else {
        return Err("recursive lemmas must match on a parameter variable".to_owned());
    };
    let Some(induction_param_index) = def
        .params
        .iter()
        .position(|param| param.name == *scrutinee_name)
    else {
        return Err("recursive lemmas must match on one of their parameters".to_owned());
    };
    if !matches!(def.params[induction_param_index].ty, SpecTy::Named { .. }) {
        return Err("recursive lemmas require a named enum parameter".to_owned());
    }
    let ctx = RecursiveLemmaContext {
        lemma_name: &def.name,
        induction_param_index,
        params: &def.params,
    };
    let mut size_map = HashMap::new();
    size_map.insert(
        def.params[induction_param_index].name.clone(),
        (def.params[induction_param_index].name.clone(), 0),
    );
    validate_recursive_lemma_stmts(&def.body, &ctx, &size_map)
}

fn type_lemmas(
    lemmas: &HashMap<String, LemmaDef>,
    declaration_order: &[String],
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    span: Span,
) -> Result<Vec<TypedLemmaDef>, LoopPrepassError> {
    let mut typed = Vec::with_capacity(declaration_order.len());
    let mut available_lemmas = HashMap::new();
    for name in declaration_order {
        let lemma = lemmas
            .get(name)
            .expect("lemma declaration order must stay in sync");
        let type_param_scope: HashSet<_> = lemma.type_params.iter().cloned().collect();
        for param in &lemma.params {
            validate_named_spec_ty(&param.ty, enum_defs, &type_param_scope).map_err(|message| {
                LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "lemma `{}` parameter `{}`: {message}",
                        lemma.name, param.name
                    ),
                }
            })?;
        }
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
        let mut visible_lemmas = available_lemmas.clone();
        visible_lemmas.insert(lemma.name.clone(), lemma.clone());
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
        infer_lemma_stmts(
            &lemma.body,
            &visible_lemmas,
            lemmas,
            pure_fns,
            enum_defs,
            &type_param_scope,
            &mut body_infer_scope,
            &param_tys,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` body: {message}", lemma.name),
        })?;
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
        })
        .and_then(|expr| {
            normalize_assert_like_predicate(expr, "lemma req").map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!("lemma `{}` req: {message}", lemma.name),
            })
        })?;
        let body = typed_lemma_stmts(
            &lemma.body,
            &visible_lemmas,
            lemmas,
            pure_fns,
            enum_defs,
            &type_param_scope,
            &mut type_scope,
            &param_tys,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` body: {message}", lemma.name),
        })?;
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
        })
        .and_then(|expr| {
            ensure_bind_free_predicate(expr, "lemma ens").map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!("lemma `{}` ens: {message}", lemma.name),
            })
        })?;
        let typed_def = TypedLemmaDef {
            name: lemma.name.clone(),
            params,
            req,
            ens,
            body,
        };
        validate_recursive_lemma(&typed_def).map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` body: {message}", lemma.name),
        })?;
        typed.push(typed_def);
        available_lemmas.insert(lemma.name.clone(), lemma.clone());
    }
    Ok(typed)
}

fn lemma_call_parts(expr: &Expr) -> Result<(&str, &[SpecTy], &[Expr]), String> {
    match expr {
        Expr::Call {
            func,
            type_args,
            args,
        } => Ok((func, type_args, args)),
        _ => Err("lemma call must be of the form `name(args...)`".to_owned()),
    }
}

fn seed_lemma_type_bindings(
    lemma_name: &str,
    type_params: &[String],
    type_args: &[SpecTy],
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
) -> Result<HashMap<String, SpecTy>, String> {
    if type_args.is_empty() {
        return Ok(HashMap::new());
    }
    if type_args.len() != type_params.len() {
        return Err(format!(
            "lemma `{lemma_name}` expects {} type arguments, found {}",
            type_params.len(),
            type_args.len()
        ));
    }
    let mut bindings = HashMap::with_capacity(type_params.len());
    for (type_param, type_arg) in type_params.iter().zip(type_args.iter()) {
        validate_named_spec_ty(type_arg, enum_defs, type_param_scope)?;
        bindings.insert(type_param.clone(), type_arg.clone());
    }
    Ok(bindings)
}

fn instantiate_lemma_param_tys(
    lemma_name: &str,
    lemma: &LemmaDef,
    bindings: &HashMap<String, SpecTy>,
) -> Result<Vec<SpecTy>, String> {
    for type_param in &lemma.type_params {
        if !bindings.contains_key(type_param) {
            return Err(format!(
                "could not infer a type for lemma `{lemma_name}` type parameter `{type_param}`"
            ));
        }
    }
    lemma
        .params
        .iter()
        .map(|param| {
            try_instantiate_spec_ty(&param.ty, bindings).ok_or_else(|| {
                format!(
                    "could not resolve type parameter(s) for lemma `{lemma_name}` parameter `{}`",
                    param.name
                )
            })
        })
        .collect()
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

#[allow(clippy::too_many_arguments)]
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
    validate_contract_expr_core(
        expr,
        pure_fns,
        enum_defs,
        spec_scope,
        params,
        allow_result,
        false,
    )
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
    allow_bare_names: bool,
) -> Result<(), String> {
    match expr {
        Expr::Bool(_) | Expr::Int(_) => Ok(()),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                return Ok(());
            }
            if allow_result && name == "result" {
                return Ok(());
            }
            if allow_bare_names && params.iter().any(|param| param == name) {
                return Ok(());
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::Interpolated(name) => {
            if params.iter().any(|param| param == name) || (allow_result && name == "result") {
                return Ok(());
            }
            if name == "result" {
                return Err("`result` is only supported in //@ ens predicates".to_owned());
            }
            Err(format!("unresolved binding `{name}` in function contract"))
        }
        Expr::SeqLit(items) => {
            for item in items {
                validate_contract_expr_core(
                    item,
                    pure_fns,
                    enum_defs,
                    spec_scope,
                    params,
                    allow_result,
                    allow_bare_names,
                )?;
            }
            Ok(())
        }
        Expr::Match { .. } => Err(unsupported_match_expr_message()),
        Expr::Bind(name) => {
            if allow_result && name == "result" {
                return Err("duplicate spec binding `?result` in //@ ens".to_owned());
            }
            spec_scope
                .bind(
                    name,
                    Span::default(),
                    None,
                    if allow_result { "ens" } else { "req" },
                )
                .map_err(|err| err.message)
        }
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(enum_defs, func) {
                let ctor = &enum_def.ctors[ctor_index];
                if ctor.fields.len() != args.len() {
                    return Err(format!(
                        "constructor `{func}` expects {} arguments, found {}",
                        ctor.fields.len(),
                        args.len()
                    ));
                }
                if enum_def.type_params.len() != type_args.len() && !type_args.is_empty() {
                    return Err(format!(
                        "constructor `{func}` expects {} type arguments, found {}",
                        enum_def.type_params.len(),
                        type_args.len()
                    ));
                }
                let scope = HashSet::new();
                for type_arg in type_args {
                    validate_named_spec_ty(type_arg, enum_defs, &scope)?;
                }
            } else {
                if !type_args.is_empty() {
                    return Err(format!(
                        "type arguments are only supported on enum constructors, found `{func}`"
                    ));
                }
                if let Some(def) = pure_fns.get(func) {
                    if def.params.len() != args.len() {
                        return Err(format!(
                            "pure function `{func}` expects {} arguments, found {}",
                            def.params.len(),
                            args.len()
                        ));
                    }
                } else if matches!(func.as_str(), "seq_len" | "seq_rev") {
                    if args.len() != 1 {
                        return Err(format!(
                            "builtin pure function `{func}` expects 1 argument, found {}",
                            args.len()
                        ));
                    }
                } else {
                    return Err(format!("unknown pure function `{func}`"));
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
                    allow_bare_names,
                )?;
            }
            Ok(())
        }
        Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Deref { base } => {
            validate_contract_expr_core(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )
        }
        Expr::Index { base, index } => {
            validate_contract_expr_core(
                base,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )?;
            validate_contract_expr_core(
                index,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )
        }
        Expr::Unary { arg, .. } => validate_contract_expr_core(
            arg,
            pure_fns,
            enum_defs,
            spec_scope,
            params,
            allow_result,
            allow_bare_names,
        ),
        Expr::Binary { lhs, rhs, .. } => {
            validate_contract_expr_core(
                lhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )?;
            validate_contract_expr_core(
                rhs,
                pure_fns,
                enum_defs,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )
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
        allow_bare_names: false,
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
            if !ctx.allow_bare_names {
                return Err(LoopPrepassError {
                    span: ctx.span,
                    display_span: None,
                    message: format!("unresolved binding `{name}` in //@ {}", ctx.kind.keyword()),
                });
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
        Expr::Interpolated(name) => {
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
                    span: ctx.span,
                    display_span: None,
                    message: format!("unsupported binding `{name}` in //@ {}", ctx.kind.keyword()),
                });
            };
            resolved.locals.insert(name.clone(), local);
            Ok(())
        }
        Expr::SeqLit(items) => {
            for item in items {
                resolve_expr_env_into(item, ctx, resolved)?;
            }
            Ok(())
        }
        Expr::Match { .. } => Err(LoopPrepassError {
            span: ctx.span,
            display_span: None,
            message: unsupported_match_expr_message(),
        }),
        Expr::Bind(name) => {
            ctx.spec_scope
                .bind(name, ctx.span, None, ctx.kind.keyword())?;
            resolved.spec_vars.insert(name.clone());
            Ok(())
        }
        Expr::Call {
            func,
            type_args,
            args,
        } => {
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
                if enum_def.type_params.len() != type_args.len() && !type_args.is_empty() {
                    return Err(LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message: format!(
                            "constructor `{func}` expects {} type arguments, found {}",
                            enum_def.type_params.len(),
                            type_args.len()
                        ),
                    });
                }
            } else {
                if !type_args.is_empty() {
                    return Err(LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message: format!(
                            "type arguments are only supported on enum constructors, found `{func}`"
                        ),
                    });
                }
                if let Some(def) = ctx.pure_fns.get(func) {
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
                } else if matches!(func.as_str(), "seq_len" | "seq_rev") {
                    if args.len() != 1 {
                        return Err(LoopPrepassError {
                            span: ctx.span,
                            display_span: None,
                            message: format!(
                                "builtin pure function `{func}` expects 1 argument, found {}",
                                args.len()
                            ),
                        });
                    }
                } else {
                    return Err(LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message: format!("unknown pure function `{func}`"),
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
        Expr::Index { base, index } => {
            resolve_expr_env_into(base, ctx, resolved)?;
            resolve_expr_env_into(index, ctx, resolved)
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
    use crate::spec::{
        EnumCtorDef, EnumDef, Expr, IntLiteral, LemmaDef, PureFnDef, PureFnParam, SpecTy,
        TypedExprKind,
    };

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
            &[],
            &[Expr::Var("arg".to_owned())],
            &pure_fns,
            &mut |expr, expected| {
                assert_eq!(expr, &Expr::Var("arg".to_owned()));
                assert_eq!(expected, Some(&SpecTy::I32));
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

    #[test]
    fn types_generic_constructor_call_with_explicit_type_args() {
        let enum_defs = HashMap::from([(
            "List".to_owned(),
            EnumDef {
                name: "List".to_owned(),
                type_params: vec!["T".to_owned()],
                ctors: vec![
                    EnumCtorDef {
                        name: "Nil".to_owned(),
                        fields: vec![],
                    },
                    EnumCtorDef {
                        name: "Cons".to_owned(),
                        fields: vec![
                            SpecTy::TypeParam("T".to_owned()),
                            SpecTy::Named {
                                name: "List".to_owned(),
                                args: vec![SpecTy::TypeParam("T".to_owned())],
                            },
                        ],
                    },
                ],
            },
        )]);

        let expr = Expr::Call {
            func: "List::Cons".to_owned(),
            type_args: vec![SpecTy::I32],
            args: vec![
                Expr::Int(IntLiteral {
                    digits: "0".to_owned(),
                    suffix: None,
                }),
                Expr::Call {
                    func: "List::Nil".to_owned(),
                    type_args: vec![SpecTy::I32],
                    args: vec![],
                },
            ],
        };

        let typed = typed_contract_expr(
            &expr,
            &HashMap::new(),
            &enum_defs,
            &mut SpecScope::default(),
            &HashMap::new(),
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
        )
        .expect("typed constructor call");

        assert_eq!(
            typed.ty,
            SpecTy::Named {
                name: "List".to_owned(),
                args: vec![SpecTy::I32],
            }
        );
        assert!(matches!(
            typed.kind,
            TypedExprKind::CtorCall {
                enum_name,
                ctor_name,
                ctor_index: 1,
                ..
            } if enum_name == "List" && ctor_name == "Cons"
        ));
    }

    #[test]
    fn types_generic_lemma_call_with_inferred_type_args() {
        let lemmas = HashMap::from([(
            "seq_concat_empty_right".to_owned(),
            LemmaDef {
                name: "seq_concat_empty_right".to_owned(),
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                req: Expr::Bool(true),
                ens: Expr::Bool(true),
                body: vec![],
            },
        )]);

        let typed = typed_lemma_call(
            &Expr::Call {
                func: "seq_concat_empty_right".to_owned(),
                type_args: vec![],
                args: vec![Expr::Interpolated("xs".to_owned())],
            },
            "seq_concat_empty_right({xs})",
            &lemmas,
            &HashMap::new(),
            &HashMap::new(),
            &mut SpecScope::default(),
            &HashMap::from([("xs".to_owned(), SpecTy::Seq(Box::new(SpecTy::I32)))]),
            &mut SpecTypeInference::default(),
        )
        .expect("typed generic lemma call");

        assert_eq!(typed.args.len(), 1);
        assert_eq!(typed.args[0].ty, SpecTy::Seq(Box::new(SpecTy::I32)));
    }

    #[test]
    fn runtime_contract_interpolation_becomes_rust_var() {
        let typed = typed_runtime_contract_expr(
            &Expr::Interpolated("x".to_owned()),
            &HashMap::new(),
            &HashMap::new(),
            &mut SpecScope::default(),
            &HashMap::from([("x".to_owned(), SpecTy::I32)]),
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
        )
        .expect("typed runtime contract expr");

        assert_eq!(
            typed,
            TypedExpr {
                ty: SpecTy::I32,
                kind: TypedExprKind::RustVar("x".to_owned()),
            }
        );
    }

    #[test]
    fn runtime_postcondition_result_stays_spec_var() {
        let typed = typed_runtime_contract_expr(
            &Expr::Var("result".to_owned()),
            &HashMap::new(),
            &HashMap::new(),
            &mut SpecScope::default(),
            &HashMap::new(),
            true,
            &SpecTy::I32,
            &mut SpecTypeInference::default(),
        )
        .expect("typed runtime postcondition expr");

        assert_eq!(
            typed,
            TypedExpr {
                ty: SpecTy::I32,
                kind: TypedExprKind::Var("result".to_owned()),
            }
        );
    }

    #[test]
    fn global_ghost_prepass_exposes_only_typed_output() {
        let ghosts = GlobalGhostPrepass {
            enums: HashMap::new(),
            typed_pure_fns: vec![TypedPureFnDef {
                name: "id".to_owned(),
                params: Vec::new(),
                body: TypedExpr {
                    ty: SpecTy::I32,
                    kind: TypedExprKind::Int(IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(crate::spec::IntSuffix::I32),
                    }),
                },
            }],
            typed_lemmas: Vec::new(),
        };

        assert_eq!(ghosts.typed_pure_fns.len(), 1);
        assert!(ghosts.typed_lemmas.is_empty());
    }
}
