//! HIR/MIR prepass that resolves directives into typed verification input.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fs;
use std::io::ErrorKind;
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use crate::directive::{
    CollectedFunctionDirectives, DirectiveAttach, DirectiveError, DirectiveKind, DirectiveOrigin,
    FunctionDirective, collect_function_directive_anchors, collect_function_directives,
    collect_ghost_blocks, collect_non_ghost_spec_comments,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{
    EnumDef, Expr, GhostMatchArm, LemmaDef, MatchBinding, MatchPattern, PureFnDef, PureFnParam,
    RawAssertion, RawPattern, RustTyKey, RustTypeExpr, SpecTy, StandaloneFnContractDef,
    StandaloneFnParam, StandaloneProofAnchor, StandaloneProofDirectiveKind, StandaloneProofPayload,
    StructDef, StructFieldTy, TypedExpr, TypedExprKind, TypedMatchArm, TypedMatchBinding,
    ValuePattern, layout_spec_ty, option_spec_ty, ptr_spec_ty,
};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    BlockCheckMode, Expr as HirExpr, ExprKind, HirId, ItemKind, Pat, PatKind, UnsafeSource,
};
use rustc_middle::mir::{BasicBlock, Body, Local, PlaceElem, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::def_id::LocalDefId;
use rustc_span::{DUMMY_SP, Span, Symbol};

const PRELUDE_GHOST_SOURCE: &str = include_str!("../lib/prelude.rs");

struct GhostSource {
    span: Span,
    text: String,
    origin: GhostSourceOrigin,
}

enum GhostSourceOrigin {
    Prelude,
    RustSource,
    AdjacentSidecar { path: PathBuf },
    ExternalSidecar { path: PathBuf },
}

struct GhostItemSink<'a> {
    enums: &'a mut Vec<EnumDef>,
    structs: &'a mut Vec<StructDef>,
    pure_fns: &'a mut Vec<PureFnDef>,
    lemmas: &'a mut Vec<LemmaDef>,
    standalone_fn_contracts: &'a mut Vec<StandaloneFnContractDef>,
}

impl GhostSourceOrigin {
    fn parse_error_message(&self, err: &crate::directive::ParseError) -> String {
        match self {
            Self::Prelude | Self::RustSource => err.to_string(),
            Self::AdjacentSidecar { path } | Self::ExternalSidecar { path } => {
                format!("{}: {err}", path.display())
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct HirBindingInfo {
    pub spans: HashMap<HirId, Span>,
    pub by_name: HashMap<Symbol, Vec<(HirId, Span)>>,
}

#[derive(Debug, Clone, Default)]
pub struct ResolvedExprEnv {
    pub locals: HashMap<String, Local>,
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
pub struct LetBindingContract {
    pub binding: NormalizedBinding,
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
pub struct RawAssertionContract {
    pub pattern: TypedRawPattern,
    pub condition: TypedExpr,
    pub resolution: ResolvedExprEnv,
    pub assertion_span: String,
}

#[derive(Debug, Clone)]
pub enum TypedRawPattern {
    Emp,
    Star(Box<TypedRawPattern>, Box<TypedRawPattern>),
    PointsTo {
        addr: TypedExpr,
        ty: TypedExpr,
        value: TypedValuePattern,
    },
    Own {
        ty: SpecTy,
        value: TypedValuePattern,
    },
    DeallocToken {
        base: TypedExpr,
        layout: TypedExpr,
    },
}

#[derive(Debug, Clone)]
pub enum TypedValuePattern {
    Bind {
        name: String,
        ty: SpecTy,
    },
    Expr(TypedExpr),
    SeqLit {
        ty: SpecTy,
        items: Vec<TypedValuePattern>,
    },
    StructLit {
        ty: SpecTy,
        fields: Vec<TypedValuePattern>,
    },
    CtorCall {
        ty: SpecTy,
        ctor_index: usize,
        args: Vec<TypedValuePattern>,
    },
}

struct RawTypingCtx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    resolution: &'a ResolvedExprEnv,
    pure_fns: &'a HashMap<String, PureFnDef>,
    enum_defs: &'a HashMap<String, EnumDef>,
    struct_defs: &'a HashMap<String, StructDef>,
    local_tys: &'a HashMap<String, SpecTy>,
}

impl<'a, 'tcx> RawTypingCtx<'a, 'tcx> {
    fn call_ctx<'b>(&'b self, type_param_scope: &'b HashSet<String>) -> SpecCallContext<'b> {
        SpecCallContext::new(
            self.pure_fns,
            self.enum_defs,
            self.struct_defs,
            type_param_scope,
        )
    }
}

#[derive(Debug, Clone)]
pub enum ControlPointDirective {
    Let(LetBindingContract),
    Assert(AssertionContract),
    Assume(AssumptionContract),
    RawAssert(Box<RawAssertionContract>),
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
    pub result_ty: SpecTy,
    pub body: Option<TypedExpr>,
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
    pub is_unsafe: bool,
    pub params: Vec<ContractParam>,
    pub req: NormalizedPredicate,
    pub raw_reqs: Vec<RawAssertionContract>,
    pub ens: TypedExpr,
    pub raw_ens: Vec<RawAssertionContract>,
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
    pub raw_reqs: Vec<RawAssertionContract>,
    pub ens: TypedExpr,
    pub ens_span: String,
    pub raw_ens: Vec<RawAssertionContract>,
    pub result: SpecTy,
}

#[derive(Debug, Clone)]
pub struct DirectivePrepass {
    pub loop_contracts: LoopContracts,
    pub control_point_directives: ControlPointDirectives,
    pub explicit_function_contract: bool,
    pub function_contract: Option<FunctionContract>,
    pub unsafe_blocks: Vec<Span>,
}

#[derive(Debug, Clone)]
struct RawGlobalGhostPrepass {
    pub enums: HashMap<String, EnumDef>,
    pub structs: HashMap<String, StructDef>,
    pub pure_fns: HashMap<String, PureFnDef>,
    pub lemmas: HashMap<String, LemmaDef>,
    pub standalone_fn_contracts: HashMap<String, StandaloneFnContractDef>,
    pure_fn_order: Vec<String>,
    lemma_order: Vec<String>,
    standalone_fn_contract_order: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct GlobalGhostPrepass {
    pub enums: HashMap<String, EnumDef>,
    pub structs: HashMap<String, StructDef>,
    pub struct_invariants: HashMap<String, TypedStructInvariant>,
    pub enum_invariants: HashMap<String, TypedEnumInvariant>,
    pub typed_pure_fns: Vec<TypedPureFnDef>,
    pub typed_lemmas: Vec<TypedLemmaDef>,
    pub standalone_fn_contracts: HashMap<String, FunctionContract>,
}

#[derive(Debug, Clone)]
pub struct TypedStructInvariant {
    pub fields: Vec<StructFieldTy>,
    pub condition: TypedExpr,
}

#[derive(Debug, Clone)]
pub struct TypedEnumInvariant {
    pub condition: TypedExpr,
}

type TypedTypeInvariants = (
    HashMap<String, TypedStructInvariant>,
    HashMap<String, TypedEnumInvariant>,
);

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
    pub standalone_fn_contracts: HashMap<String, FunctionContract>,
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
    let mut raw_ghosts = match compute_raw_global_ghost_prepass(tcx, anchor_span) {
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
    if let Err(error) = collect_rust_struct_defs(tcx, &mut raw_ghosts.structs, anchor_span) {
        return Err(vec![VerificationResult {
            function: "prepass".to_owned(),
            status: VerificationStatus::Unsupported,
            span: error
                .display_span
                .unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(error.span)),
            message: error.message,
        }]);
    }
    if let Err(error) =
        collect_enum_variant_struct_defs(&raw_ghosts.enums, &mut raw_ghosts.structs, anchor_span)
    {
        return Err(vec![VerificationResult {
            function: "prepass".to_owned(),
            status: VerificationStatus::Unsupported,
            span: error
                .display_span
                .unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(error.span)),
            message: error.message,
        }]);
    }
    let raw_ghosts = match normalize_global_ghost_prepass(&raw_ghosts, anchor_span) {
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
            Ok(mut prepass) => {
                let path = tcx.def_path_str(def_id.to_def_id());
                if prepass.explicit_function_contract
                    && raw_ghosts.standalone_fn_contracts.contains_key(&path)
                {
                    errors.push(VerificationResult {
                        function: path.clone(),
                        status: VerificationStatus::Unsupported,
                        span: tcx
                            .sess
                            .source_map()
                            .span_to_diagnostic_string(item.span),
                        message: "function contract is declared both on the function body and in a standalone contract declaration".to_owned(),
                    });
                    continue;
                }
                if !prepass.explicit_function_contract
                    && let Some(contract) = ghosts.standalone_fn_contracts.get(&path)
                {
                    prepass.function_contract = Some(contract.clone());
                }
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
            standalone_fn_contracts: ghosts.standalone_fn_contracts.clone(),
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
    validate_global_spec_comment_positions(tcx)?;
    let sources = collect_global_ghost_sources(tcx, anchor_span)?;

    let mut enum_defs = Vec::new();
    let mut struct_defs = Vec::new();
    let mut pure_fn_defs = Vec::new();
    let mut lemma_defs = Vec::new();
    let mut standalone_fn_contract_defs = Vec::new();
    for source in sources {
        let mut sink = GhostItemSink {
            enums: &mut enum_defs,
            structs: &mut struct_defs,
            pure_fns: &mut pure_fn_defs,
            lemmas: &mut lemma_defs,
            standalone_fn_contracts: &mut standalone_fn_contract_defs,
        };
        collect_ghost_items_in_source(&source.text, source.span, &source.origin, &mut sink)?;
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

    let mut structs = HashMap::new();
    for struct_def in struct_defs {
        if structs
            .insert(struct_def.name.clone(), struct_def.clone())
            .is_some()
        {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: format!("duplicate struct name `{}`", struct_def.name),
            });
        }
    }

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

    let mut standalone_fn_contracts = HashMap::new();
    let mut standalone_fn_contract_order = Vec::with_capacity(standalone_fn_contract_defs.len());
    for def in standalone_fn_contract_defs {
        if standalone_fn_contracts
            .insert(def.path.clone(), def.clone())
            .is_some()
        {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: format!("duplicate function contract declaration `{}`", def.path),
            });
        }
        standalone_fn_contract_order.push(def.path);
    }

    Ok(RawGlobalGhostPrepass {
        enums,
        structs,
        pure_fns,
        lemmas,
        standalone_fn_contracts,
        pure_fn_order,
        lemma_order,
        standalone_fn_contract_order,
    })
}

fn collect_rust_struct_defs<'tcx>(
    tcx: TyCtxt<'tcx>,
    struct_defs: &mut HashMap<String, StructDef>,
    anchor_span: Span,
) -> Result<(), LoopPrepassError> {
    let mut visiting = HashSet::new();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::Fn { .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        for local in body.borrow().local_decls.iter() {
            collect_rust_struct_defs_for_ty(tcx, local.ty, struct_defs, &mut visiting).map_err(
                |message| LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message,
                },
            )?;
        }
    }
    Ok(())
}

fn collect_rust_struct_defs_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    struct_defs: &mut HashMap<String, StructDef>,
    visiting: &mut HashSet<String>,
) -> Result<(), String> {
    match ty.kind() {
        TyKind::Ref(_, inner, _) => {
            collect_rust_struct_defs_for_ty(tcx, *inner, struct_defs, visiting)
        }
        TyKind::Tuple(fields) => {
            for field in fields.iter() {
                collect_rust_struct_defs_for_ty(tcx, field, struct_defs, visiting)?;
            }
            Ok(())
        }
        TyKind::Adt(adt_def, args) => {
            if tcx.def_path_str(adt_def.did()) == "std::vec::Vec" {
                if let Some(inner) = args.types().next() {
                    collect_rust_struct_defs_for_ty(tcx, inner, struct_defs, visiting)?;
                }
                return Ok(());
            }
            if !adt_def.is_struct() {
                return Ok(());
            }
            if !args.is_empty() {
                return Err(format!("generic structs are unsupported: {ty:?}"));
            }
            let name = tcx.def_path_str(adt_def.did());
            if struct_defs.contains_key(&name) || !visiting.insert(name.clone()) {
                return Ok(());
            }
            let mut fields = Vec::new();
            for field in adt_def.non_enum_variant().fields.iter() {
                let field_ty = field.ty(tcx, args);
                collect_rust_struct_defs_for_ty(tcx, field_ty, struct_defs, visiting)?;
                fields.push(StructFieldTy {
                    name: field.name.to_string(),
                    ty: spec_ty_for_rust_ty(tcx, field_ty)?,
                });
            }
            visiting.remove(&name);
            struct_defs.insert(
                name.clone(),
                StructDef {
                    name,
                    type_params: Vec::new(),
                    fields,
                    invariant: None,
                },
            );
            Ok(())
        }
        _ => Ok(()),
    }
}

fn collect_enum_variant_struct_defs(
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &mut HashMap<String, StructDef>,
    anchor_span: Span,
) -> Result<(), LoopPrepassError> {
    for enum_def in enum_defs.values() {
        for ctor in &enum_def.ctors {
            if ctor.field_names.is_empty() || !ctor.field_names.iter().all(Option::is_some) {
                continue;
            }
            let name = format!("{}::{}", enum_def.name, ctor.name);
            let fields = ctor
                .field_names
                .iter()
                .zip(&ctor.fields)
                .map(|(name, ty)| StructFieldTy {
                    name: name.clone().expect("checked named variant field"),
                    ty: ty.clone(),
                })
                .collect();
            let def = StructDef {
                name: name.clone(),
                type_params: enum_def.type_params.clone(),
                fields,
                invariant: None,
            };
            if struct_defs.insert(name.clone(), def).is_some() {
                return Err(LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("duplicate struct name `{name}`"),
                });
            }
        }
    }
    Ok(())
}

fn validate_global_spec_comment_positions<'tcx>(tcx: TyCtxt<'tcx>) -> Result<(), LoopPrepassError> {
    let mut files: HashMap<_, (String, Vec<(usize, usize)>)> = HashMap::new();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let loc = tcx.sess.source_map().lookup_char_pos(item.span.lo());
        let Some(source) = loc.file.src.as_deref() else {
            continue;
        };
        let entry = files
            .entry(loc.file.start_pos)
            .or_insert_with(|| (source.to_owned(), Vec::new()));
        if matches!(item.kind, ItemKind::Fn { .. }) {
            let start = item.span.lo().0.saturating_sub(loc.file.start_pos.0) as usize;
            let end = item.span.hi().0.saturating_sub(loc.file.start_pos.0) as usize;
            entry.1.push((start, end));
        }
    }

    for (source, function_ranges) in files.into_values() {
        for comment in collect_non_ghost_spec_comments(&source) {
            let in_function = function_ranges
                .iter()
                .any(|(start, end)| *start <= comment.start_offset && comment.start_offset < *end);
            if !in_function {
                return Err(LoopPrepassError {
                    span: DUMMY_SP,
                    display_span: None,
                    message: format!(
                        "spec comment is not attached to a function contract, ghost item, ghost command, or loop invariant: {}",
                        comment.line_text
                    ),
                });
            }
        }
    }

    Ok(())
}

fn type_global_ghost_prepass(
    raw: &RawGlobalGhostPrepass,
    anchor_span: Span,
) -> Result<GlobalGhostPrepass, LoopPrepassError> {
    let typed_pure_fns = type_pure_fns(
        &raw.pure_fns,
        &raw.pure_fn_order,
        &raw.enums,
        &raw.structs,
        anchor_span,
    )?;
    let (struct_invariants, enum_invariants) =
        type_type_invariants(&raw.structs, &raw.enums, &raw.pure_fns, anchor_span)?;
    let typed_lemmas = type_lemmas(
        &raw.lemmas,
        &raw.lemma_order,
        &raw.pure_fns,
        &raw.enums,
        &raw.structs,
        anchor_span,
    )?;
    let standalone_fn_contracts = type_standalone_fn_contracts(
        &raw.standalone_fn_contracts,
        &raw.standalone_fn_contract_order,
        &raw.pure_fns,
        &raw.enums,
        &raw.structs,
        anchor_span,
    )?;
    Ok(GlobalGhostPrepass {
        enums: raw.enums.clone(),
        structs: raw.structs.clone(),
        struct_invariants,
        enum_invariants,
        typed_pure_fns,
        typed_lemmas,
        standalone_fn_contracts,
    })
}

fn normalize_global_ghost_prepass(
    raw: &RawGlobalGhostPrepass,
    anchor_span: Span,
) -> Result<RawGlobalGhostPrepass, LoopPrepassError> {
    let structs = raw
        .structs
        .iter()
        .map(|(name, def)| {
            normalize_struct_def(def, &raw.enums, &raw.structs)
                .map(|def| (name.clone(), def))
                .map_err(|message| LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("struct `{}`: {message}", def.name),
                })
        })
        .collect::<Result<HashMap<_, _>, _>>()?;
    let pure_fns = raw
        .pure_fns
        .iter()
        .map(|(name, def)| {
            normalize_pure_fn_def(def, &raw.enums, &structs)
                .map(|def| (name.clone(), def))
                .map_err(|message| LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("pure function `{}`: {message}", def.name),
                })
        })
        .collect::<Result<HashMap<_, _>, _>>()?;
    let lemmas = raw
        .lemmas
        .iter()
        .map(|(name, def)| {
            normalize_lemma_def(def, &raw.enums, &structs)
                .map(|def| (name.clone(), def))
                .map_err(|message| LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("lemma `{}`: {message}", def.name),
                })
        })
        .collect::<Result<HashMap<_, _>, _>>()?;
    let standalone_fn_contracts = raw
        .standalone_fn_contracts
        .iter()
        .map(|(path, def)| {
            normalize_standalone_fn_contract_def(def, &raw.enums, &structs)
                .map(|def| (path.clone(), def))
                .map_err(|message| LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("function contract declaration `{}`: {message}", def.path),
                })
        })
        .collect::<Result<HashMap<_, _>, _>>()?;
    Ok(RawGlobalGhostPrepass {
        enums: raw.enums.clone(),
        structs,
        pure_fns,
        lemmas,
        standalone_fn_contracts,
        pure_fn_order: raw.pure_fn_order.clone(),
        lemma_order: raw.lemma_order.clone(),
        standalone_fn_contract_order: raw.standalone_fn_contract_order.clone(),
    })
}

fn type_type_invariants(
    structs: &HashMap<String, StructDef>,
    enums: &HashMap<String, EnumDef>,
    pure_fns: &HashMap<String, PureFnDef>,
    anchor_span: Span,
) -> Result<TypedTypeInvariants, LoopPrepassError> {
    let mut struct_invariants = HashMap::new();
    for def in structs.values() {
        let Some(invariant) = &def.invariant else {
            continue;
        };
        let params = def
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.ty.clone()))
            .collect::<HashMap<_, _>>();
        let type_params = def.type_params.iter().cloned().collect::<HashSet<_>>();
        let condition = typed_contract_expr_with_expected(
            invariant,
            pure_fns,
            enums,
            structs,
            &type_params,
            &mut SpecScope::default(),
            &params,
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
            true,
            Some(&SpecTy::Bool),
        )
        .map_err(|message| LoopPrepassError {
            span: anchor_span,
            display_span: None,
            message: format!("struct `{}` invariant: {message}", def.name),
        })?;
        if condition.ty != SpecTy::Bool {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: format!("struct `{}` invariant must have type `bool`", def.name),
            });
        }
        struct_invariants.insert(
            def.name.clone(),
            TypedStructInvariant {
                fields: def.fields.clone(),
                condition,
            },
        );
    }

    let mut enum_invariants = HashMap::new();
    for def in enums.values() {
        let Some(invariant) = &def.invariant else {
            continue;
        };
        let type_params = def.type_params.iter().cloned().collect::<HashSet<_>>();
        let self_ty = enum_result_ty(
            def,
            def.type_params
                .iter()
                .map(|param| SpecTy::TypeParam(param.clone()))
                .collect(),
        );
        let params = HashMap::from([("self".to_owned(), self_ty.clone())]);
        let condition = typed_contract_expr_with_expected(
            invariant,
            pure_fns,
            enums,
            structs,
            &type_params,
            &mut SpecScope::default(),
            &params,
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
            true,
            Some(&SpecTy::Bool),
        )
        .map_err(|message| LoopPrepassError {
            span: anchor_span,
            display_span: None,
            message: format!("enum `{}` invariant: {message}", def.name),
        })?;
        if condition.ty != SpecTy::Bool {
            return Err(LoopPrepassError {
                span: anchor_span,
                display_span: None,
                message: format!("enum `{}` invariant must have type `bool`", def.name),
            });
        }
        enum_invariants.insert(def.name.clone(), TypedEnumInvariant { condition });
    }
    Ok((struct_invariants, enum_invariants))
}

fn collect_global_ghost_sources<'tcx>(
    tcx: TyCtxt<'tcx>,
    anchor_span: Span,
) -> Result<Vec<GhostSource>, LoopPrepassError> {
    let mut sources = vec![GhostSource {
        span: anchor_span,
        text: PRELUDE_GHOST_SOURCE.to_owned(),
        origin: GhostSourceOrigin::Prelude,
    }];
    let mut seen_sources = HashSet::new();
    let external_spec_roots = ExternalSpecRoots::from_env();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let loc = tcx.sess.source_map().lookup_char_pos(item.span.lo());
        let key = loc.file.start_pos;
        if seen_sources.insert(key) {
            sources.push(GhostSource {
                span: item.span,
                text: loc
                    .file
                    .src
                    .as_ref()
                    .map_or_else(String::new, |src| src.as_str().to_owned()),
                origin: GhostSourceOrigin::RustSource,
            });
            let path = loc.file.name.prefer_local().to_string();
            let source_path = Path::new(&path);
            if let Some(source) = read_adjacent_sidecar_ghost_source(source_path, item.span)? {
                sources.push(source);
            }
            if let Some(source) = read_external_sidecar_ghost_source(
                external_spec_roots.as_ref(),
                source_path,
                item.span,
            )? {
                sources.push(source);
            }
        }
    }
    Ok(sources)
}

struct ExternalSpecRoots {
    subject_root: PathBuf,
    spec_root: PathBuf,
}

impl ExternalSpecRoots {
    fn from_env() -> Option<Self> {
        let subject_root = std::env::var_os("TSUNO_SUBJECT_ROOT").map(PathBuf::from)?;
        let spec_root = std::env::var_os("TSUNO_SPEC_ROOT").map(PathBuf::from)?;
        Some(Self {
            subject_root: subject_root.canonicalize().unwrap_or(subject_root),
            spec_root: spec_root.canonicalize().unwrap_or(spec_root),
        })
    }
}

fn read_adjacent_sidecar_ghost_source(
    source_path: &Path,
    span: Span,
) -> Result<Option<GhostSource>, LoopPrepassError> {
    let Some(file_name) = source_path.file_name().and_then(|name| name.to_str()) else {
        return Ok(None);
    };
    let sidecar_path = source_path.with_file_name(format!("{file_name}.tsuno"));
    let text = match fs::read_to_string(&sidecar_path) {
        Ok(text) => text,
        Err(err) if err.kind() == ErrorKind::NotFound => return Ok(None),
        Err(err) => {
            return Err(LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "failed to read sidecar spec file `{}`: {err}",
                    sidecar_path.display()
                ),
            });
        }
    };
    Ok(Some(GhostSource {
        span,
        text: format!("/*@\n{text}\n*/"),
        origin: GhostSourceOrigin::AdjacentSidecar { path: sidecar_path },
    }))
}

fn read_external_sidecar_ghost_source(
    roots: Option<&ExternalSpecRoots>,
    source_path: &Path,
    span: Span,
) -> Result<Option<GhostSource>, LoopPrepassError> {
    let Some(roots) = roots else {
        return Ok(None);
    };
    let absolute_source_path = if source_path.is_absolute() {
        source_path.to_owned()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::new())
            .join(source_path)
    };
    let absolute_source_path = absolute_source_path
        .canonicalize()
        .unwrap_or(absolute_source_path);
    let Ok(relative_path) = absolute_source_path.strip_prefix(&roots.subject_root) else {
        return Ok(None);
    };
    let Some(file_name) = relative_path.file_name().and_then(|name| name.to_str()) else {
        return Ok(None);
    };
    let external_path = roots
        .spec_root
        .join(relative_path)
        .with_file_name(format!("{file_name}.tsuno"));
    let text = match fs::read_to_string(&external_path) {
        Ok(text) => text,
        Err(err) if err.kind() == ErrorKind::NotFound => return Ok(None),
        Err(err) => {
            return Err(LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "failed to read external spec file `{}`: {err}",
                    external_path.display()
                ),
            });
        }
    };
    Ok(Some(GhostSource {
        span,
        text: format!("/*@\n{text}\n*/"),
        origin: GhostSourceOrigin::ExternalSidecar {
            path: external_path,
        },
    }))
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
    scoped: HashMap<String, Span>,
}

impl SpecScope {
    fn bind_let(
        &mut self,
        name: &str,
        span: Span,
        display_span: Option<String>,
        scope_span: Option<Span>,
    ) -> Result<(), LoopPrepassError> {
        if self.bound.contains(name) {
            return Err(LoopPrepassError {
                span,
                display_span,
                message: format!("duplicate spec binding `{name}` in //@ let"),
            });
        }
        self.bound.insert(name.to_owned());
        self.visible.insert(name.to_owned());
        self.ordered.push(name.to_owned());
        if let Some(scope_span) = scope_span {
            self.scoped.insert(name.to_owned(), scope_span);
        }
        Ok(())
    }

    fn prune_expired(&mut self, anchor_span: Span) {
        let expired: Vec<_> = self
            .scoped
            .iter()
            .filter_map(|(name, scope_span)| {
                if scope_contains(*scope_span, anchor_span) {
                    None
                } else {
                    Some(name.clone())
                }
            })
            .collect();
        for name in expired {
            self.scoped.remove(&name);
            self.visible.remove(&name);
            self.bound.remove(&name);
        }
    }

    fn typed_ordered(
        &self,
        inferred: &mut SpecTypeInference,
    ) -> Result<Vec<SpecVarBinding>, String> {
        typed_spec_vars_for_names(&self.ordered, inferred)
    }
}

fn scope_contains(scope_span: Span, anchor_span: Span) -> bool {
    scope_span.lo() <= anchor_span.lo() && anchor_span.hi() <= scope_span.hi()
}

fn typed_expr_contains_bind(expr: &TypedExpr) -> bool {
    match &expr.kind {
        TypedExprKind::Bool(_)
        | TypedExprKind::Int(_)
        | TypedExprKind::Var(_)
        | TypedExprKind::RustVar(_)
        | TypedExprKind::RustType(_) => false,
        TypedExprKind::SeqLit(items) | TypedExprKind::StructLit { fields: items } => {
            items.iter().any(typed_expr_contains_bind)
        }
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
        | TypedExprKind::VariantSelector { base, .. }
        | TypedExprKind::Cast { arg: base }
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

fn typed_rust_type_expr(expr: &RustTypeExpr) -> TypedExpr {
    TypedExpr {
        ty: SpecTy::RustTy,
        kind: TypedExprKind::RustType(RustTyKey::new(expr.text.clone())),
    }
}

fn normalize_assert_like_predicate(
    expr: TypedExpr,
    kind: &str,
) -> Result<NormalizedPredicate, String> {
    Ok(NormalizedPredicate {
        bindings: Vec::new(),
        condition: ensure_bind_free_predicate(expr, kind)?,
    })
}

fn ensure_bind_free_predicate(expr: TypedExpr, kind: &str) -> Result<TypedExpr, String> {
    if typed_expr_contains_bind(&expr) {
        return Err(format!("new spec bindings are not allowed in {kind}"));
    }
    Ok(expr)
}

fn bind_free_normalized_predicate(
    bindings: Vec<NormalizedBinding>,
    expr: TypedExpr,
    kind: &str,
) -> Result<NormalizedPredicate, String> {
    Ok(NormalizedPredicate {
        bindings,
        condition: ensure_bind_free_predicate(expr, kind)?,
    })
}

#[derive(Clone, Copy)]
struct SpecCallContext<'a> {
    pure_fns: &'a HashMap<String, PureFnDef>,
    enum_defs: &'a HashMap<String, EnumDef>,
    struct_defs: &'a HashMap<String, StructDef>,
    type_param_scope: &'a HashSet<String>,
}

impl<'a> SpecCallContext<'a> {
    fn new(
        pure_fns: &'a HashMap<String, PureFnDef>,
        enum_defs: &'a HashMap<String, EnumDef>,
        struct_defs: &'a HashMap<String, StructDef>,
        type_param_scope: &'a HashSet<String>,
    ) -> Self {
        Self {
            pure_fns,
            enum_defs,
            struct_defs,
            type_param_scope,
        }
    }
}

struct ExprResolutionContext<'a> {
    call_ctx: SpecCallContext<'a>,
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

fn constrain_let_binding_ty(
    name: &str,
    inferred_ty: InferredExprTy,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    inferred.ensure_var(name);
    match inferred_ty {
        InferredExprTy::Known(ty) => inferred.constrain(name, &ty),
        InferredExprTy::SpecVar(other) => inferred.union(name, &other),
        InferredExprTy::Unknown => Ok(()),
    }
}

fn unify_spec_tys(lhs: &SpecTy, rhs: &SpecTy) -> Result<SpecTy, String> {
    match (lhs, rhs) {
        (SpecTy::Bool, SpecTy::Bool) => Ok(SpecTy::Bool),
        (SpecTy::IntLiteral, SpecTy::IntLiteral) => Ok(SpecTy::IntLiteral),
        (SpecTy::Int, rhs) if is_integer_spec_ty(rhs) => Ok(SpecTy::Int),
        (lhs, SpecTy::Int) if is_integer_spec_ty(lhs) => Ok(SpecTy::Int),
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
        (
            SpecTy::Struct {
                name: lhs_name,
                args: lhs_args,
            },
            SpecTy::Struct {
                name: rhs_name,
                args: rhs_args,
            },
        ) if lhs_name == rhs_name && lhs_args.len() == rhs_args.len() => {
            let mut args = Vec::with_capacity(lhs_args.len());
            for (lhs_arg, rhs_arg) in lhs_args.iter().zip(rhs_args) {
                args.push(unify_spec_tys(lhs_arg, rhs_arg)?);
            }
            Ok(SpecTy::Struct {
                name: lhs_name.clone(),
                args,
            })
        }
        (
            SpecTy::Enum {
                name: lhs_name,
                args: lhs_args,
            },
            SpecTy::Enum {
                name: rhs_name,
                args: rhs_args,
            },
        ) if lhs_name == rhs_name && lhs_args.len() == rhs_args.len() => {
            let mut args = Vec::with_capacity(lhs_args.len());
            for (lhs_arg, rhs_arg) in lhs_args.iter().zip(rhs_args) {
                args.push(unify_spec_tys(lhs_arg, rhs_arg)?);
            }
            Ok(SpecTy::Enum {
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
        SpecTy::RustTy => "RustTy".to_owned(),
        SpecTy::Int => "Int".to_owned(),
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
        SpecTy::Struct { name, args } => {
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
        SpecTy::Enum { name, args } => {
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

fn nat_spec_ty() -> SpecTy {
    SpecTy::Enum {
        name: "Nat".to_owned(),
        args: vec![],
    }
}

fn is_nat_spec_ty(ty: &SpecTy) -> bool {
    matches!(
        ty,
        SpecTy::Enum { name, args } if name == "Nat" && args.is_empty()
    )
}

fn type_int_expr_as(
    lit: &crate::spec::IntLiteral,
    expected: Option<&SpecTy>,
    enum_defs: &HashMap<String, EnumDef>,
) -> Result<TypedExpr, String> {
    let ty = match (lit.suffix, expected) {
        (None, Some(expected)) if is_nat_spec_ty(expected) => nat_spec_ty(),
        _ => lit.spec_ty(),
    };
    if is_nat_spec_ty(&ty) {
        return type_nat_literal_expr(&lit.digits, enum_defs);
    }
    Ok(TypedExpr {
        ty,
        kind: TypedExprKind::Int(lit.clone()),
    })
}

fn type_nat_literal_expr(
    digits: &str,
    enum_defs: &HashMap<String, EnumDef>,
) -> Result<TypedExpr, String> {
    let value = digits
        .parse::<u128>()
        .map_err(|_| format!("invalid Nat literal `{digits}`"))?;
    let nat_def = enum_defs
        .get("Nat")
        .ok_or_else(|| "Nat is missing from the prelude".to_owned())?;
    let (zero_index, _) = nat_def
        .ctor("Zero")
        .ok_or_else(|| "Nat is missing `Zero`".to_owned())?;
    let mut expr = TypedExpr {
        ty: nat_spec_ty(),
        kind: TypedExprKind::CtorCall {
            enum_name: "Nat".to_owned(),
            ctor_name: "Zero".to_owned(),
            ctor_index: zero_index,
            args: vec![],
        },
    };
    if value == 0 {
        return Ok(expr);
    }
    let bit_len = u128::BITS - value.leading_zeros();
    for bit_index in (0..bit_len).rev() {
        let func = if (value >> bit_index) & 1 == 0 {
            "nat_bit0"
        } else {
            "nat_bit1"
        };
        expr = TypedExpr {
            ty: nat_spec_ty(),
            kind: TypedExprKind::PureCall {
                func: func.to_owned(),
                args: vec![expr],
            },
        };
    }
    Ok(expr)
}

fn is_integer_spec_ty(ty: &SpecTy) -> bool {
    matches!(
        ty,
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
            | SpecTy::Usize
    )
}

fn is_numeric_spec_ty(ty: &SpecTy) -> bool {
    is_integer_spec_ty(ty) || is_nat_spec_ty(ty)
}

fn is_concrete_integer_spec_ty(ty: &SpecTy) -> bool {
    is_integer_spec_ty(ty) && *ty != SpecTy::IntLiteral
}

fn is_fully_inferred_spec_ty(ty: &SpecTy) -> bool {
    match ty {
        SpecTy::IntLiteral => false,
        SpecTy::Tuple(items) => items.iter().all(is_fully_inferred_spec_ty),
        SpecTy::Struct { args, .. } => args.iter().all(is_fully_inferred_spec_ty),
        SpecTy::Enum { args, .. } => args.iter().all(is_fully_inferred_spec_ty),
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
        TyKind::RawPtr(_, _) => Ok(ptr_spec_ty()),
        TyKind::Param(param) => Ok(SpecTy::TypeParam(param.name.to_string())),
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
            let name = tcx.def_path_str(adt_def.did());
            Ok(SpecTy::Struct {
                name,
                args: Vec::new(),
            })
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

fn resolve_named_struct_spec_ty(
    ty: &SpecTy,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    type_params: &HashSet<String>,
) -> Result<SpecTy, String> {
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
        | SpecTy::Usize => Ok(ty.clone()),
        SpecTy::Seq(inner) => Ok(SpecTy::Seq(Box::new(resolve_named_struct_spec_ty(
            inner,
            enum_defs,
            struct_defs,
            type_params,
        )?))),
        SpecTy::Tuple(items) => items
            .iter()
            .map(|item| resolve_named_struct_spec_ty(item, enum_defs, struct_defs, type_params))
            .collect::<Result<Vec<_>, _>>()
            .map(SpecTy::Tuple),
        SpecTy::Struct { name, args } => args
            .iter()
            .map(|arg| resolve_named_struct_spec_ty(arg, enum_defs, struct_defs, type_params))
            .collect::<Result<Vec<_>, _>>()
            .map(|args| SpecTy::Struct {
                name: name.clone(),
                args,
            }),
        SpecTy::Enum { name, args } => {
            if let Some(enum_def) = enum_defs.get(name) {
                if enum_def.type_params.len() != args.len() {
                    return Err(format!(
                        "spec type `{name}` expects {} type arguments, found {}",
                        enum_def.type_params.len(),
                        args.len()
                    ));
                }
                let args = args
                    .iter()
                    .map(|arg| {
                        resolve_named_struct_spec_ty(arg, enum_defs, struct_defs, type_params)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(SpecTy::Enum {
                    name: name.clone(),
                    args,
                });
            }
            let Some(struct_def) = struct_defs.get(name) else {
                return Err(format!("unknown spec type `{name}`"));
            };
            if struct_def.type_params.len() != args.len() {
                return Err(format!(
                    "spec type `{name}` expects {} type arguments, found {}",
                    struct_def.type_params.len(),
                    args.len()
                ));
            }
            let args = args
                .iter()
                .map(|arg| resolve_named_struct_spec_ty(arg, enum_defs, struct_defs, type_params))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SpecTy::Struct {
                name: name.clone(),
                args,
            })
        }
        SpecTy::TypeParam(name) => type_params
            .contains(name)
            .then(|| ty.clone())
            .ok_or_else(|| format!("unbound spec type parameter `{name}`")),
        SpecTy::Ref(inner) => Ok(SpecTy::Ref(Box::new(resolve_named_struct_spec_ty(
            inner,
            enum_defs,
            struct_defs,
            type_params,
        )?))),
        SpecTy::Mut(inner) => Ok(SpecTy::Mut(Box::new(resolve_named_struct_spec_ty(
            inner,
            enum_defs,
            struct_defs,
            type_params,
        )?))),
    }
}

fn resolve_own_rust_type_expr(
    ty: &RustTypeExpr,
    struct_defs: &HashMap<String, StructDef>,
    type_params: &HashSet<String>,
) -> Result<SpecTy, String> {
    rust_type_text_to_own_spec_ty(&ty.text, struct_defs, type_params)
}

fn rust_type_text_to_own_spec_ty(
    text: &str,
    struct_defs: &HashMap<String, StructDef>,
    type_params: &HashSet<String>,
) -> Result<SpecTy, String> {
    match text {
        "()" => Ok(SpecTy::Tuple(vec![])),
        "bool" => Ok(SpecTy::Bool),
        "i8" => Ok(SpecTy::I8),
        "i16" => Ok(SpecTy::I16),
        "i32" => Ok(SpecTy::I32),
        "i64" => Ok(SpecTy::I64),
        "isize" => Ok(SpecTy::Isize),
        "u8" => Ok(SpecTy::U8),
        "u16" => Ok(SpecTy::U16),
        "u32" => Ok(SpecTy::U32),
        "u64" => Ok(SpecTy::U64),
        "usize" => Ok(SpecTy::Usize),
        raw if raw.starts_with("*const ") || raw.starts_with("*mut ") => Ok(ptr_spec_ty()),
        raw if raw.starts_with("&mut ") => {
            Ok(SpecTy::Mut(Box::new(rust_type_text_to_own_spec_ty(
                raw.trim_start_matches("&mut ").trim(),
                struct_defs,
                type_params,
            )?)))
        }
        raw if raw.starts_with('&') => Ok(SpecTy::Ref(Box::new(rust_type_text_to_own_spec_ty(
            raw.trim_start_matches('&').trim(),
            struct_defs,
            type_params,
        )?))),
        type_param if type_params.contains(type_param) => {
            Ok(SpecTy::TypeParam(type_param.to_owned()))
        }
        rust_struct => resolve_own_rust_struct_ty(rust_struct, struct_defs),
    }
}

fn resolve_own_rust_struct_ty(
    text: &str,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<SpecTy, String> {
    if text.contains('<') {
        return Err(format!(
            "generic Rust type `{text}` in `Own` is unsupported"
        ));
    }
    if let Some(def) = struct_defs
        .get(text)
        .or_else(|| prelude_struct_defs().get(text))
    {
        return Ok(SpecTy::Struct {
            name: def.name.clone(),
            args: Vec::new(),
        });
    }
    let matches = struct_defs
        .values()
        .chain(prelude_struct_defs().values())
        .filter(|def| {
            def.name
                .rsplit("::")
                .next()
                .is_some_and(|short| short == text)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [def] => Ok(SpecTy::Struct {
            name: def.name.clone(),
            args: Vec::new(),
        }),
        [] => Err(format!("unknown Rust type `{text}` in `Own`")),
        _ => Err(format!("ambiguous Rust type `{text}` in `Own`")),
    }
}

fn normalize_pure_fn_param(
    param: &PureFnParam,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    type_params: &HashSet<String>,
) -> Result<PureFnParam, String> {
    Ok(PureFnParam {
        name: param.name.clone(),
        ty: resolve_named_struct_spec_ty(&param.ty, enum_defs, struct_defs, type_params)?,
    })
}

fn normalize_struct_def(
    def: &StructDef,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<StructDef, String> {
    let type_params = def.type_params.iter().cloned().collect::<HashSet<_>>();
    let fields = def
        .fields
        .iter()
        .map(|field| {
            Ok(StructFieldTy {
                name: field.name.clone(),
                ty: resolve_named_struct_spec_ty(&field.ty, enum_defs, struct_defs, &type_params)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(StructDef {
        name: def.name.clone(),
        type_params: def.type_params.clone(),
        fields,
        invariant: def.invariant.clone(),
    })
}

fn normalize_pure_fn_def(
    def: &PureFnDef,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<PureFnDef, String> {
    let type_params = def.type_params.iter().cloned().collect::<HashSet<_>>();
    Ok(PureFnDef {
        name: def.name.clone(),
        type_params: def.type_params.clone(),
        params: def
            .params
            .iter()
            .map(|param| normalize_pure_fn_param(param, enum_defs, struct_defs, &type_params))
            .collect::<Result<Vec<_>, _>>()?,
        result_ty: resolve_named_struct_spec_ty(
            &def.result_ty,
            enum_defs,
            struct_defs,
            &type_params,
        )?,
        body: def.body.clone(),
    })
}

fn normalize_lemma_def(
    def: &LemmaDef,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<LemmaDef, String> {
    let type_params = def.type_params.iter().cloned().collect::<HashSet<_>>();
    Ok(LemmaDef {
        name: def.name.clone(),
        is_unsafe: def.is_unsafe,
        type_params: def.type_params.clone(),
        params: def
            .params
            .iter()
            .map(|param| normalize_pure_fn_param(param, enum_defs, struct_defs, &type_params))
            .collect::<Result<Vec<_>, _>>()?,
        req: def.req.clone(),
        raw_reqs: def.raw_reqs.clone(),
        ens: def.ens.clone(),
        raw_ens: def.raw_ens.clone(),
        body: def.body.clone(),
    })
}

fn normalize_standalone_fn_contract_def(
    def: &StandaloneFnContractDef,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<StandaloneFnContractDef, String> {
    let type_params = def.type_params.iter().cloned().collect::<HashSet<_>>();
    Ok(StandaloneFnContractDef {
        path: def.path.clone(),
        is_unsafe: def.is_unsafe,
        type_params: def.type_params.clone(),
        params: def
            .params
            .iter()
            .map(|param| {
                Ok(StandaloneFnParam {
                    name: param.name.clone(),
                    rust_ty: param.rust_ty.clone(),
                    ty: resolve_named_struct_spec_ty(
                        &param.ty,
                        enum_defs,
                        struct_defs,
                        &type_params,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, String>>()?,
        result_rust_ty: def.result_rust_ty.clone(),
        result_ty: resolve_named_struct_spec_ty(
            &def.result_ty,
            enum_defs,
            struct_defs,
            &type_params,
        )?,
        req: def.req.clone(),
        raw_reqs: def.raw_reqs.clone(),
        ens: def.ens.clone(),
        raw_ens: def.raw_ens.clone(),
        proof_blocks: def.proof_blocks.clone(),
    })
}

fn validate_named_spec_ty(
    ty: &SpecTy,
    enum_defs: &HashMap<String, EnumDef>,
    type_params: &HashSet<String>,
) -> Result<(), String> {
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
        | SpecTy::Usize => Ok(()),
        SpecTy::Seq(inner) => validate_named_spec_ty(inner, enum_defs, type_params),
        SpecTy::Tuple(items) => {
            for item in items {
                validate_named_spec_ty(item, enum_defs, type_params)?;
            }
            Ok(())
        }
        SpecTy::Struct { args, .. } => {
            for arg in args {
                validate_named_spec_ty(arg, enum_defs, type_params)?;
            }
            Ok(())
        }
        SpecTy::Enum { name, args } => {
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
        SpecTy::Ref(inner) | SpecTy::Mut(inner) => {
            validate_named_spec_ty(inner, enum_defs, type_params)
        }
    }
}

fn enum_result_ty(enum_def: &EnumDef, type_args: Vec<SpecTy>) -> SpecTy {
    SpecTy::Enum {
        name: enum_def.name.clone(),
        args: type_args,
    }
}

fn try_instantiate_spec_ty(ty: &SpecTy, bindings: &HashMap<String, SpecTy>) -> Option<SpecTy> {
    match ty {
        SpecTy::Bool => Some(SpecTy::Bool),
        SpecTy::RustTy => Some(SpecTy::RustTy),
        SpecTy::Int => Some(SpecTy::Int),
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
        SpecTy::Struct { name, args } => args
            .iter()
            .map(|arg| try_instantiate_spec_ty(arg, bindings))
            .collect::<Option<Vec<_>>>()
            .map(|args| SpecTy::Struct {
                name: name.clone(),
                args,
            }),
        SpecTy::Enum { name, args } => args
            .iter()
            .map(|arg| try_instantiate_spec_ty(arg, bindings))
            .collect::<Option<Vec<_>>>()
            .map(|args| SpecTy::Enum {
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

fn prelude_struct_defs() -> &'static HashMap<String, StructDef> {
    static STRUCTS: OnceLock<HashMap<String, StructDef>> = OnceLock::new();
    STRUCTS.get_or_init(|| {
        let mut enum_defs = Vec::new();
        let mut struct_defs = Vec::new();
        let mut pure_fn_defs = Vec::new();
        let mut lemma_defs = Vec::new();
        let mut standalone_fn_contract_defs = Vec::new();
        collect_ghost_items_in_source(
            PRELUDE_GHOST_SOURCE,
            DUMMY_SP,
            &GhostSourceOrigin::Prelude,
            &mut GhostItemSink {
                enums: &mut enum_defs,
                structs: &mut struct_defs,
                pure_fns: &mut pure_fn_defs,
                lemmas: &mut lemma_defs,
                standalone_fn_contracts: &mut standalone_fn_contract_defs,
            },
        )
        .unwrap_or_else(|err| panic!("prelude ghost source must parse: {}", err.message));
        let enums = enum_defs
            .into_iter()
            .map(|def| (def.name.clone(), def))
            .collect::<HashMap<_, _>>();
        let raw_structs = struct_defs
            .into_iter()
            .map(|def| (def.name.clone(), def))
            .collect::<HashMap<_, _>>();
        raw_structs
            .values()
            .map(|def| {
                normalize_struct_def(def, &enums, &raw_structs)
                    .map(|def| (def.name.clone(), def))
                    .expect("prelude struct definitions must normalize")
            })
            .collect()
    })
}

fn struct_fields_for_ty(
    ty: &SpecTy,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<Option<Vec<StructFieldTy>>, String> {
    let SpecTy::Struct { name, args } = ty else {
        return Ok(None);
    };
    let Some(def) = struct_defs
        .get(name)
        .or_else(|| prelude_struct_defs().get(name))
    else {
        return Ok(None);
    };
    if def.type_params.len() != args.len() {
        return Err(format!(
            "spec struct `{name}` expects {} type arguments, found {}",
            def.type_params.len(),
            args.len()
        ));
    }
    let bindings = def
        .type_params
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect::<HashMap<_, _>>();
    def.fields
        .iter()
        .map(|field| {
            Ok(StructFieldTy {
                name: field.name.clone(),
                ty: try_instantiate_spec_ty(&field.ty, &bindings)
                    .ok_or_else(|| format!("unbound spec type parameter in `{name}`"))?,
            })
        })
        .collect::<Result<Vec<_>, String>>()
        .map(Some)
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
        SpecTy::Enum { name, args } => match actual {
            SpecTy::Enum {
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
        SpecTy::Struct { name, args } => match actual {
            SpecTy::Struct {
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
    let SpecTy::Enum { name, args } = expected else {
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
            if ctor.field_names.len() != ctor.fields.len() {
                return Err(LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "enum `{}` constructor `{}` has mismatched field metadata",
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

fn type_struct_lit_expr(
    name: &str,
    fields: &[crate::spec::StructLitField],
    expected: Option<&SpecTy>,
    struct_defs: &HashMap<String, StructDef>,
    type_value: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    let expected_ty = match expected {
        Some(SpecTy::Struct {
            name: expected_name,
            ..
        }) if expected_name == name => expected.cloned(),
        Some(other) => {
            return Err(format!(
                "struct literal `{name}` requires `{name}`, found `{}`",
                display_spec_ty(other)
            ));
        }
        None => struct_defs.get(name).map(|def| SpecTy::Struct {
            name: def.name.clone(),
            args: Vec::new(),
        }),
    };
    let Some(expected_ty) = expected_ty else {
        return Err(format!("unknown spec struct `{name}`"));
    };
    let expected_fields = struct_fields_for_ty(&expected_ty, struct_defs)?
        .ok_or_else(|| format!("unknown spec struct `{name}`"))?;
    let mut seen = HashSet::new();
    let mut typed_fields = Vec::with_capacity(fields.len());
    for field in fields {
        if !seen.insert(field.name.clone()) {
            return Err(format!(
                "struct literal `{name}` contains duplicate field `{}`",
                field.name
            ));
        }
        let expected_field = expected_fields
            .iter()
            .find(|item| item.name == field.name)
            .map(|field| &field.ty);
        let Some(expected_field) = expected_field else {
            return Err(format!("unknown field `{}` in `{name}`", field.name));
        };
        let typed = type_value(&field.value, Some(expected_field))?;
        typed_fields.push(typed);
    }
    for expected_field in &expected_fields {
        if !seen.contains(&expected_field.name) {
            return Err(format!(
                "struct literal `{name}` is missing field `{}`",
                expected_field.name
            ));
        }
    }
    let mut by_name = fields
        .iter()
        .zip(typed_fields)
        .map(|(field, typed)| (field.name.clone(), typed))
        .collect::<HashMap<_, _>>();
    typed_fields = expected_fields
        .iter()
        .map(|field| by_name.remove(&field.name).expect("checked field exists"))
        .collect();
    Ok(TypedExpr {
        ty: expected_ty,
        kind: TypedExprKind::StructLit {
            fields: typed_fields,
        },
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
    if matches!(func, "isize::MAX") {
        if !type_args.is_empty() {
            return Err(format!(
                "type arguments are not supported on builtin pure function `{func}`"
            ));
        }
        if !args.is_empty() {
            return Err(format!(
                "builtin pure function `{func}` expects 0 arguments, found {}",
                args.len()
            ));
        }
        return Ok(Some(InferredExprTy::Known(SpecTy::Isize)));
    }
    if !matches!(func, "seq_len") {
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
    let SpecTy::Seq(_) = arg_ty else {
        return Err(format!(
            "builtin pure function `{func}` requires `Seq<T>`, found `{}`",
            display_spec_ty(&arg_ty)
        ));
    };
    Ok(Some(match func {
        "seq_len" => InferredExprTy::Known(nat_spec_ty()),
        _ => unreachable!("checked builtin pure function"),
    }))
}

fn type_builtin_pure_call(
    func: &str,
    type_args: &[SpecTy],
    args: &[Expr],
    type_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<Option<TypedExpr>, String> {
    if matches!(func, "isize::MAX") {
        if !type_args.is_empty() {
            return Err(format!(
                "type arguments are not supported on builtin pure function `{func}`"
            ));
        }
        if !args.is_empty() {
            return Err(format!(
                "builtin pure function `{func}` expects 0 arguments, found {}",
                args.len()
            ));
        }
        return Ok(Some(TypedExpr {
            ty: SpecTy::Isize,
            kind: TypedExprKind::PureCall {
                func: func.to_owned(),
                args: Vec::new(),
            },
        }));
    }
    if !matches!(func, "seq_len") {
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
    let SpecTy::Seq(_) = &typed_arg.ty else {
        return Err(format!(
            "builtin pure function `{func}` requires `Seq<T>`, found `{}`",
            display_spec_ty(&typed_arg.ty)
        ));
    };
    Ok(Some(TypedExpr {
        ty: match func {
            "seq_len" => nat_spec_ty(),
            _ => unreachable!("checked builtin pure function"),
        },
        kind: TypedExprKind::PureCall {
            func: func.to_owned(),
            args: vec![typed_arg],
        },
    }))
}

fn unresolved_pure_fn_type_param<'a>(
    def: &'a PureFnDef,
    bindings: &HashMap<String, SpecTy>,
) -> Option<&'a str> {
    def.type_params
        .iter()
        .find(|type_param| !bindings.contains_key(*type_param))
        .map(String::as_str)
}

fn seed_pure_fn_type_bindings(
    func: &str,
    def: &PureFnDef,
    type_args: &[SpecTy],
    call_ctx: SpecCallContext<'_>,
) -> Result<HashMap<String, SpecTy>, String> {
    if type_args.is_empty() {
        return Ok(HashMap::new());
    }
    if def.type_params.len() != type_args.len() {
        return Err(format!(
            "pure function `{func}` expects {} type arguments, found {}",
            def.type_params.len(),
            type_args.len()
        ));
    }
    let mut bindings = HashMap::with_capacity(def.type_params.len());
    for (type_param, type_arg) in def.type_params.iter().zip(type_args.iter()) {
        validate_named_spec_ty(type_arg, call_ctx.enum_defs, call_ctx.type_param_scope)?;
        bindings.insert(type_param.clone(), type_arg.clone());
    }
    Ok(bindings)
}

fn validate_ctor_type_args(
    func: &str,
    enum_def: &EnumDef,
    type_args: &[SpecTy],
    call_ctx: SpecCallContext<'_>,
) -> Result<(), String> {
    if enum_def.type_params.len() != type_args.len() && !type_args.is_empty() {
        return Err(format!(
            "constructor `{func}` expects {} type arguments, found {}",
            enum_def.type_params.len(),
            type_args.len()
        ));
    }
    for type_arg in type_args {
        validate_named_spec_ty(type_arg, call_ctx.enum_defs, call_ctx.type_param_scope)?;
    }
    Ok(())
}

fn validate_pure_call_signature(
    func: &str,
    type_args: &[SpecTy],
    args_len: usize,
    call_ctx: SpecCallContext<'_>,
) -> Result<(), String> {
    if let Some(def) = call_ctx.pure_fns.get(func) {
        if def.params.len() != args_len {
            return Err(format!(
                "pure function `{func}` expects {} arguments, found {}",
                def.params.len(),
                args_len
            ));
        }
        seed_pure_fn_type_bindings(func, def, type_args, call_ctx)?;
        return Ok(());
    }
    if matches!(func, "seq_len" | "isize::MAX") {
        if !type_args.is_empty() {
            return Err(format!(
                "type arguments are not supported on builtin pure function `{func}`"
            ));
        }
        if func == "isize::MAX" {
            if args_len != 0 {
                return Err(format!(
                    "builtin pure function `{func}` expects 0 arguments, found {args_len}"
                ));
            }
            return Ok(());
        }
        if args_len != 1 {
            return Err(format!(
                "builtin pure function `{func}` expects 1 argument, found {args_len}"
            ));
        }
        return Ok(());
    }
    Err(format!("unknown pure function `{func}`"))
}

fn instantiate_pure_fn_param_tys(
    func: &str,
    def: &PureFnDef,
    bindings: &HashMap<String, SpecTy>,
) -> Result<Vec<SpecTy>, String> {
    def.params
        .iter()
        .map(|param| {
            try_instantiate_spec_ty(&param.ty, bindings).ok_or_else(|| {
                match unresolved_pure_fn_type_param(def, bindings) {
                    Some(type_param) => format!(
                        "could not infer a type for pure function `{func}` type parameter `{type_param}`"
                    ),
                    None => format!(
                        "could not resolve type parameter(s) for pure function `{func}` parameter `{}`",
                        param.name
                    ),
                }
            })
        })
        .collect()
}

fn instantiate_pure_fn_result_ty(
    func: &str,
    def: &PureFnDef,
    bindings: &HashMap<String, SpecTy>,
) -> Result<SpecTy, String> {
    try_instantiate_spec_ty(&def.result_ty, bindings).ok_or_else(|| {
        match unresolved_pure_fn_type_param(def, bindings) {
            Some(type_param) => format!(
                "could not infer a type for pure function `{func}` type parameter `{type_param}`"
            ),
            None => {
                format!("could not resolve type parameter(s) for pure function `{func}` result")
            }
        }
    })
}

fn infer_pure_call_result_ty(
    func: &str,
    type_args: &[SpecTy],
    args: &[Expr],
    call_ctx: SpecCallContext<'_>,
    inferred: &mut SpecTypeInference,
    infer_arg: &mut impl FnMut(
        &Expr,
        Option<&SpecTy>,
        &mut SpecTypeInference,
    ) -> Result<InferredExprTy, String>,
) -> Result<InferredExprTy, String> {
    if let Some(result) = infer_builtin_pure_call(func, type_args, args, &mut |arg, expected| {
        infer_arg(arg, expected, inferred)
    })? {
        return Ok(result);
    }
    let Some(def) = call_ctx.pure_fns.get(func) else {
        return Err(format!("unknown pure function `{func}`"));
    };
    if def.params.len() != args.len() {
        return Err(format!(
            "pure function `{func}` expects {} arguments, found {}",
            def.params.len(),
            args.len()
        ));
    }
    let mut bindings = seed_pure_fn_type_bindings(func, def, type_args, call_ctx)?;
    let mut arg_tys = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&def.params) {
        let expected = try_instantiate_spec_ty(&param.ty, &bindings);
        let arg_ty = infer_arg(arg, expected.as_ref(), inferred)?;
        let actual_ty = match &arg_ty {
            InferredExprTy::Known(actual) => Some(actual.clone()),
            InferredExprTy::SpecVar(name) => inferred.resolved_ty(name),
            InferredExprTy::Unknown => None,
        };
        if let Some(actual) = actual_ty.as_ref() {
            infer_type_param_bindings(&param.ty, actual, &mut bindings)?;
        }
        arg_tys.push(arg_ty);
    }
    if def
        .type_params
        .iter()
        .all(|type_param| bindings.contains_key(type_param))
    {
        let param_tys = instantiate_pure_fn_param_tys(func, def, &bindings)?;
        for (arg_ty, param_ty) in arg_tys.iter().zip(param_tys.iter()) {
            constrain_expr_ty(inferred, arg_ty, param_ty)?;
        }
    }
    Ok(InferredExprTy::Known(instantiate_pure_fn_result_ty(
        func, def, &bindings,
    )?))
}

fn type_pure_call(
    func: &str,
    type_args: &[SpecTy],
    args: &[Expr],
    call_ctx: SpecCallContext<'_>,
    type_arg: &mut impl FnMut(&Expr, Option<&SpecTy>) -> Result<TypedExpr, String>,
) -> Result<TypedExpr, String> {
    if let Some(typed) = type_builtin_pure_call(func, type_args, args, type_arg)? {
        return Ok(typed);
    }
    let Some(def) = call_ctx.pure_fns.get(func) else {
        return Err(format!("unknown pure function `{func}`"));
    };
    if def.params.len() != args.len() {
        return Err(format!(
            "pure function `{func}` expects {} arguments, found {}",
            def.params.len(),
            args.len()
        ));
    }
    let mut bindings = seed_pure_fn_type_bindings(func, def, type_args, call_ctx)?;
    let mut typed_args = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&def.params) {
        let expected = try_instantiate_spec_ty(&param.ty, &bindings);
        let typed_arg = type_arg(arg, expected.as_ref())?;
        infer_type_param_bindings(&param.ty, &typed_arg.ty, &mut bindings)?;
        typed_args.push(typed_arg);
    }
    let param_tys = instantiate_pure_fn_param_tys(func, def, &bindings)?;
    for ((typed_arg, param), param_ty) in typed_args
        .iter()
        .zip(def.params.iter())
        .zip(param_tys.iter())
    {
        let unified = unify_spec_tys(&typed_arg.ty, param_ty)?;
        if unified != *param_ty {
            return Err(format!(
                "pure function `{func}` parameter `{}` expects `{}`, found `{}`",
                param.name,
                display_spec_ty(param_ty),
                display_spec_ty(&typed_arg.ty)
            ));
        }
    }
    let result_ty = instantiate_pure_fn_result_ty(func, def, &bindings)?;
    Ok(TypedExpr {
        ty: result_ty,
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
    let mut scope = HashSet::new();
    for type_arg in type_args {
        collect_spec_ty_type_params(type_arg, &mut scope);
    }
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

fn collect_spec_ty_type_params(ty: &SpecTy, out: &mut HashSet<String>) {
    match ty {
        SpecTy::Seq(inner) | SpecTy::Ref(inner) | SpecTy::Mut(inner) => {
            collect_spec_ty_type_params(inner, out);
        }
        SpecTy::Tuple(items) => {
            for item in items {
                collect_spec_ty_type_params(item, out);
            }
        }
        SpecTy::Struct { args, .. } | SpecTy::Enum { args, .. } => {
            for arg in args {
                collect_spec_ty_type_params(arg, out);
            }
        }
        SpecTy::TypeParam(name) => {
            out.insert(name.clone());
        }
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
        | SpecTy::Usize => {}
    }
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
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        struct_defs,
        type_param_scope,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        allow_bare_names,
        None,
    )?;
    let InferredExprTy::Known(SpecTy::Enum {
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
            struct_defs,
            type_param_scope,
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
            struct_defs,
            type_param_scope,
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
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        struct_defs,
        type_param_scope,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        allow_bare_names,
        None,
    )?;
    let SpecTy::Enum {
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
            struct_defs,
            type_param_scope,
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
            struct_defs,
            type_param_scope,
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
fn infer_contract_expr_types_in_scope(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        struct_defs,
        type_param_scope,
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
fn infer_common_expr_types_with_expected(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
    inferred: &mut SpecTypeInference,
    expected: Option<&SpecTy>,
    infer_expr: &mut impl FnMut(
        &Expr,
        Option<&SpecTy>,
        &mut SpecTypeInference,
    ) -> Result<InferredExprTy, String>,
) -> Result<Option<InferredExprTy>, String> {
    match expr {
        Expr::Bool(_) => Ok(Some(InferredExprTy::Known(SpecTy::Bool))),
        Expr::Int(lit) => Ok(Some(InferredExprTy::Known(match (lit.suffix, expected) {
            (None, Some(expected)) if is_nat_spec_ty(expected) => nat_spec_ty(),
            _ => lit.spec_ty(),
        }))),
        Expr::RustType(_) => Ok(Some(InferredExprTy::Known(SpecTy::RustTy))),
        Expr::SeqLit(items) => Ok(Some(infer_seq_lit_expr_types(
            items,
            expected,
            &mut |item, expected| infer_expr(item, expected, inferred),
        )?)),
        Expr::StructLit { name, fields } => {
            let expected_ty = match expected {
                Some(SpecTy::Struct {
                    name: expected_name,
                    ..
                }) if expected_name == name => expected.cloned(),
                Some(_) => None,
                None => call_ctx.struct_defs.get(name).map(|def| SpecTy::Struct {
                    name: def.name.clone(),
                    args: Vec::new(),
                }),
            };
            let Some(expected_ty) = expected_ty else {
                return Ok(Some(InferredExprTy::Unknown));
            };
            let expected_fields = struct_fields_for_ty(&expected_ty, call_ctx.struct_defs)?
                .ok_or_else(|| format!("unknown spec struct `{name}`"))?;
            for field in fields {
                let field_expected = expected_fields
                    .iter()
                    .find(|item| item.name == field.name)
                    .map(|field| &field.ty);
                infer_expr(&field.value, field_expected, inferred)?;
            }
            Ok(Some(InferredExprTy::Known(expected_ty)))
        }
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(call_ctx.enum_defs, func) {
                Ok(Some(InferredExprTy::Known(infer_ctor_call_result_ty(
                    func,
                    enum_def,
                    ctor_index,
                    type_args,
                    args,
                    call_ctx.enum_defs,
                    expected,
                    &mut |arg, expected| infer_expr(arg, expected, inferred),
                )?)))
            } else {
                Ok(Some(infer_pure_call_result_ty(
                    func, type_args, args, call_ctx, inferred, infer_expr,
                )?))
            }
        }
        Expr::Field { base, name } => Ok(Some(infer_named_field_expr_type(
            infer_expr(base, None, inferred)?,
            name,
            call_ctx.struct_defs,
        )?)),
        Expr::TupleField { base, .. } => Ok(Some(infer_tuple_field_expr_type(infer_expr(
            base, None, inferred,
        )?)?)),
        Expr::VariantSelector {
            base,
            enum_name,
            ctor_name,
            type_args,
        } => Ok(Some(infer_variant_selector_ty(
            infer_expr(base, None, inferred)?,
            enum_name,
            ctor_name,
            type_args,
            call_ctx.enum_defs,
            call_ctx.struct_defs,
        )?)),
        Expr::Index { base, index } => Ok(Some(infer_seq_index_expr_types(
            base,
            index,
            &mut |expr, expected| infer_expr(expr, expected, inferred),
        )?)),
        Expr::Deref { base } => {
            let base_ty = infer_expr(base, None, inferred)?;
            Ok(Some(match base_ty {
                InferredExprTy::Known(SpecTy::Ref(inner))
                | InferredExprTy::Known(SpecTy::Mut(inner)) => InferredExprTy::Known(*inner),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => InferredExprTy::Unknown,
                InferredExprTy::Known(other) => {
                    return Err(format!(
                        "dereference requires Ref<T> or Mut<T>, found `{}`",
                        display_spec_ty(&other)
                    ));
                }
            }))
        }
        Expr::Cast { arg, ty } => {
            let arg_ty = infer_expr(arg, None, inferred)?;
            let Some(arg_ty) = known_spec_ty(&arg_ty) else {
                return Ok(Some(InferredExprTy::Known(ty.clone())));
            };
            if !is_integer_spec_ty(&arg_ty) || !is_integer_spec_ty(ty) {
                return Err(format!(
                    "casts require integer types, found `{}` and `{}`",
                    display_spec_ty(&arg_ty),
                    display_spec_ty(ty)
                ));
            }
            Ok(Some(InferredExprTy::Known(ty.clone())))
        }
        Expr::Unary { op, arg } => {
            let arg_ty = infer_expr(arg, None, inferred)?;
            Ok(Some(match op {
                crate::spec::UnaryOp::Not => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::Bool)?;
                    InferredExprTy::Known(SpecTy::Bool)
                }
                crate::spec::UnaryOp::Neg => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::IntLiteral)?;
                    arg_ty
                }
            }))
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs_ty = infer_expr(lhs, None, inferred)?;
            let rhs_expected = match (op, known_spec_ty(&lhs_ty)) {
                (
                    crate::spec::BinaryOp::Eq
                    | crate::spec::BinaryOp::Ne
                    | crate::spec::BinaryOp::Concat,
                    Some(ty),
                ) if is_empty_seq_lit(rhs) => Some(ty),
                _ => None,
            };
            let rhs_ty = infer_expr(rhs, rhs_expected.as_ref(), inferred)?;
            Ok(Some(match op {
                crate::spec::BinaryOp::Eq | crate::spec::BinaryOp::Ne => {
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    InferredExprTy::Known(SpecTy::Bool)
                }
                crate::spec::BinaryOp::And | crate::spec::BinaryOp::Or => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Bool)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Bool)?;
                    InferredExprTy::Known(SpecTy::Bool)
                }
                crate::spec::BinaryOp::Lt
                | crate::spec::BinaryOp::Le
                | crate::spec::BinaryOp::Gt
                | crate::spec::BinaryOp::Ge => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                    let _ = numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)?;
                    InferredExprTy::Known(SpecTy::Bool)
                }
                crate::spec::BinaryOp::Add
                | crate::spec::BinaryOp::Sub
                | crate::spec::BinaryOp::Mul
                | crate::spec::BinaryOp::BitAnd => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                    numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)?
                }
                crate::spec::BinaryOp::Rem => {
                    let lhs = known_spec_ty(&lhs_ty);
                    let rhs = known_spec_ty(&rhs_ty);
                    if lhs.as_ref().is_some_and(is_nat_spec_ty)
                        || rhs.as_ref().is_some_and(is_nat_spec_ty)
                    {
                        InferredExprTy::Known(SpecTy::Int)
                    } else {
                        constrain_expr_ty(inferred, &lhs_ty, &SpecTy::IntLiteral)?;
                        constrain_expr_ty(inferred, &rhs_ty, &SpecTy::IntLiteral)?;
                        numeric_expr_result_ty(inferred, &lhs_ty, &rhs_ty)?
                    }
                }
                crate::spec::BinaryOp::Concat => {
                    let Some(lhs_ty) = known_spec_ty(&lhs_ty) else {
                        return Ok(Some(InferredExprTy::Unknown));
                    };
                    let Some(rhs_ty) = known_spec_ty(&rhs_ty) else {
                        return Ok(Some(InferredExprTy::Unknown));
                    };
                    let unified = unify_spec_tys(&lhs_ty, &rhs_ty)?;
                    if !matches!(unified, SpecTy::Seq(_)) {
                        return Err(format!(
                            "sequence concatenation requires `Seq<T>`, found `{}` and `{}`",
                            display_spec_ty(&lhs_ty),
                            display_spec_ty(&rhs_ty)
                        ));
                    }
                    InferredExprTy::Known(unified)
                }
            }))
        }
        Expr::Var(_) | Expr::Interpolated(_) | Expr::Match { .. } => Ok(None),
    }
}

#[allow(clippy::too_many_arguments)]
fn infer_runtime_contract_expr_types(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    let type_param_scope = HashSet::new();
    infer_runtime_contract_expr_types_in_scope(
        expr,
        pure_fns,
        enum_defs,
        struct_defs,
        &type_param_scope,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
    )
}

#[allow(clippy::too_many_arguments)]
fn infer_runtime_contract_expr_types_in_scope(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        struct_defs,
        type_param_scope,
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
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        Expr::Int(lit) => Ok(InferredExprTy::Known(match (lit.suffix, expected) {
            (None, Some(expected)) if is_nat_spec_ty(expected) => nat_spec_ty(),
            _ => lit.spec_ty(),
        })),
        Expr::RustType(_) => Ok(InferredExprTy::Known(SpecTy::RustTy)),
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
            struct_defs,
            type_param_scope,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        ),
        _ => infer_common_expr_types_with_expected(
            expr,
            SpecCallContext {
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
            },
            inferred,
            expected,
            &mut |expr, expected, inferred| {
                infer_contract_expr_types_with_expected(
                    expr,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                    allow_bare_names,
                    expected,
                )
            },
        )?
        .ok_or_else(|| "unexpected contract expression variant".to_owned()),
    }
}

fn infer_body_expr_types(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    infer_body_expr_types_with_expected(
        expr, call_ctx, kind, spec_scope, local_tys, inferred, false, None,
    )
}

#[allow(clippy::too_many_arguments)]
fn infer_body_expr_types_with_expected(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
    allow_bare_names: bool,
    expected: Option<&SpecTy>,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(lit) => Ok(InferredExprTy::Known(match (lit.suffix, expected) {
            (None, Some(expected)) if is_nat_spec_ty(expected) => nat_spec_ty(),
            _ => lit.spec_ty(),
        })),
        Expr::RustType(_) => Ok(InferredExprTy::Known(SpecTy::RustTy)),
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
        Expr::Match { .. } => Err(unsupported_match_expr_message()),
        _ => infer_common_expr_types_with_expected(
            expr,
            call_ctx,
            inferred,
            expected,
            &mut |expr, expected, inferred| {
                infer_body_expr_types_with_expected(
                    expr,
                    call_ctx,
                    kind,
                    spec_scope,
                    local_tys,
                    inferred,
                    allow_bare_names,
                    expected,
                )
            },
        )?
        .ok_or_else(|| format!("unexpected expression in //@ {}", kind.keyword())),
    }
}

fn expr_base(base: &Expr) -> &Expr {
    base
}

fn infer_named_field_expr_type(
    base_ty: InferredExprTy,
    name: &str,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<InferredExprTy, String> {
    match base_ty {
        InferredExprTy::Known(ty @ SpecTy::Struct { .. }) => {
            Ok(struct_fields_for_ty(&ty, struct_defs)?
                .and_then(|fields| {
                    fields
                        .into_iter()
                        .find(|field| field.name == name)
                        .map(|field| InferredExprTy::Known(field.ty))
                })
                .unwrap_or(InferredExprTy::Unknown))
        }
        InferredExprTy::Known(SpecTy::Ref(inner)) if name == "deref" => {
            Ok(InferredExprTy::Known(*inner))
        }
        InferredExprTy::Known(SpecTy::Ref(_)) if name == "ptr" => {
            Ok(InferredExprTy::Known(ptr_spec_ty()))
        }
        InferredExprTy::Known(SpecTy::Mut(inner)) if name == "cur" || name == "fin" => {
            Ok(InferredExprTy::Known(*inner))
        }
        InferredExprTy::Known(SpecTy::Mut(_)) if name == "ptr" => {
            Ok(InferredExprTy::Known(ptr_spec_ty()))
        }
        InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
        InferredExprTy::Known(other) => Err(format!(
            "field access requires a struct, Ref<T>, or Mut<T>. found `{}`",
            display_spec_ty(&other)
        )),
    }
}

fn infer_tuple_field_expr_type(base_ty: InferredExprTy) -> Result<InferredExprTy, String> {
    match base_ty {
        InferredExprTy::Known(SpecTy::Tuple(_)) => Ok(InferredExprTy::Unknown),
        InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
        InferredExprTy::Known(SpecTy::Struct { .. }) => {
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
fn typed_contract_expr_in_scope(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        struct_defs,
        type_param_scope,
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
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<TypedExpr, String> {
    let type_param_scope = HashSet::new();
    typed_runtime_contract_expr_in_scope(
        expr,
        pure_fns,
        enum_defs,
        struct_defs,
        &type_param_scope,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
    )
}

#[allow(clippy::too_many_arguments)]
fn typed_runtime_contract_expr_in_scope(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        struct_defs,
        type_param_scope,
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
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
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
        Expr::Int(lit) => type_int_expr_as(lit, expected, enum_defs),
        Expr::RustType(expr) => Ok(typed_rust_type_expr(expr)),
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
                struct_defs,
                type_param_scope,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::StructLit { name, fields } => type_struct_lit_expr(
            name,
            fields,
            expected,
            struct_defs,
            &mut |value, expected| {
                typed_contract_expr_with_expected(
                    value,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                    allow_bare_names,
                    expected,
                )
            },
        ),
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
            struct_defs,
            type_param_scope,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            allow_bare_names,
            expected,
        ),
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
                            struct_defs,
                            type_param_scope,
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
                type_pure_call(
                    func,
                    type_args,
                    args,
                    SpecCallContext {
                        pure_fns,
                        enum_defs,
                        struct_defs,
                        type_param_scope,
                    },
                    &mut |arg, expected| {
                        typed_contract_expr_with_expected(
                            arg,
                            pure_fns,
                            enum_defs,
                            struct_defs,
                            type_param_scope,
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
            }
        }
        Expr::Field { base, name } => {
            let base = typed_contract_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_named_field_expr(base, name, struct_defs)
        }
        Expr::TupleField { base, index } => {
            let base = typed_contract_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
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
        Expr::VariantSelector {
            base,
            enum_name,
            ctor_name,
            type_args,
        } => {
            let base = typed_contract_expr_with_expected(
                base,
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_variant_selector(
                base,
                enum_name,
                ctor_name,
                type_args,
                enum_defs,
                struct_defs,
            )
        }
        Expr::Index { base, index } => type_seq_index_expr(base, index, &mut |expr, expected| {
            typed_contract_expr_with_expected(
                expr,
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
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
                struct_defs,
                type_param_scope,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_deref_expr(base)
        }
        Expr::Cast { arg, ty } => {
            let arg = typed_contract_expr_with_expected(
                arg,
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_cast_expr(arg, ty)
        }
        Expr::Unary { op, arg } => {
            let arg = typed_contract_expr_with_expected(
                arg,
                pure_fns,
                enum_defs,
                struct_defs,
                type_param_scope,
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
                struct_defs,
                type_param_scope,
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
                struct_defs,
                type_param_scope,
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
    call_ctx: SpecCallContext<'_>,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<TypedExpr, String> {
    typed_body_expr_with_expected(
        expr, call_ctx, kind, spec_scope, local_tys, inferred, false, None,
    )
}

#[allow(clippy::too_many_arguments)]
fn typed_body_expr_with_expected(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
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
        Expr::Int(lit) => type_int_expr_as(lit, expected, call_ctx.enum_defs),
        Expr::RustType(expr) => Ok(typed_rust_type_expr(expr)),
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
                call_ctx,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                expected,
            )
        }),
        Expr::StructLit { name, fields } => type_struct_lit_expr(
            name,
            fields,
            expected,
            call_ctx.struct_defs,
            &mut |value, expected| {
                typed_body_expr_with_expected(
                    value,
                    call_ctx,
                    kind,
                    spec_scope,
                    local_tys,
                    inferred,
                    allow_bare_names,
                    expected,
                )
            },
        ),
        Expr::Match { .. } => Err(unsupported_match_expr_message()),
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(call_ctx.enum_defs, func) {
                type_ctor_call(
                    func,
                    enum_def,
                    ctor_index,
                    type_args,
                    args,
                    call_ctx.enum_defs,
                    expected,
                    &mut |arg, expected| {
                        typed_body_expr_with_expected(
                            arg,
                            call_ctx,
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
                type_pure_call(func, type_args, args, call_ctx, &mut |arg, expected| {
                    typed_body_expr_with_expected(
                        arg,
                        call_ctx,
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
                call_ctx,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_named_field_expr(base, name, call_ctx.struct_defs)
        }
        Expr::TupleField { base, index } => {
            let base = typed_body_expr_with_expected(
                expr_base(base),
                call_ctx,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_tuple_field_expr(base, *index)
        }
        Expr::VariantSelector {
            base,
            enum_name,
            ctor_name,
            type_args,
        } => {
            let base = typed_body_expr_with_expected(
                expr_base(base),
                call_ctx,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_variant_selector(
                base,
                enum_name,
                ctor_name,
                type_args,
                call_ctx.enum_defs,
                call_ctx.struct_defs,
            )
        }
        Expr::Index { base, index } => type_seq_index_expr(base, index, &mut |expr, expected| {
            typed_body_expr_with_expected(
                expr,
                call_ctx,
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
                call_ctx,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_deref_expr(base)
        }
        Expr::Cast { arg, ty } => {
            let arg = typed_body_expr_with_expected(
                arg,
                call_ctx,
                kind,
                spec_scope,
                local_tys,
                inferred,
                allow_bare_names,
                None,
            )?;
            type_cast_expr(arg, ty)
        }
        Expr::Unary { op, arg } => {
            let arg = typed_body_expr_with_expected(
                arg,
                call_ctx,
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
                call_ctx,
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
                call_ctx,
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
        crate::spec::BinaryOp::Add
        | crate::spec::BinaryOp::Sub
        | crate::spec::BinaryOp::Mul
        | crate::spec::BinaryOp::BitAnd => {
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
        crate::spec::BinaryOp::Rem => {
            if !is_numeric_spec_ty(&lhs.ty) && lhs.ty != SpecTy::IntLiteral {
                return Err(format!(
                    "remainder requires numbers, found `{}`",
                    display_spec_ty(&lhs.ty)
                ));
            }
            if !is_numeric_spec_ty(&rhs.ty) && rhs.ty != SpecTy::IntLiteral {
                return Err(format!(
                    "remainder requires numbers, found `{}`",
                    display_spec_ty(&rhs.ty)
                ));
            }
            let ty = if is_nat_spec_ty(&lhs.ty) || is_nat_spec_ty(&rhs.ty) {
                SpecTy::Int
            } else {
                unify_spec_tys(&lhs.ty, &rhs.ty)?
            };
            Ok(TypedExpr {
                ty,
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

fn type_named_field_expr(
    base: TypedExpr,
    name: &str,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<TypedExpr, String> {
    match (base.ty.clone(), name) {
        (SpecTy::Ref(inner), "deref") => {
            return Ok(TypedExpr {
                ty: *inner,
                kind: TypedExprKind::Field {
                    base: Box::new(base),
                    name: name.to_owned(),
                    index: 0,
                },
            });
        }
        (SpecTy::Ref(_), "ptr") => {
            return Ok(TypedExpr {
                ty: ptr_spec_ty(),
                kind: TypedExprKind::Field {
                    base: Box::new(base),
                    name: name.to_owned(),
                    index: 1,
                },
            });
        }
        (SpecTy::Mut(inner), "cur") => {
            return Ok(TypedExpr {
                ty: *inner,
                kind: TypedExprKind::Field {
                    base: Box::new(base),
                    name: name.to_owned(),
                    index: 0,
                },
            });
        }
        (SpecTy::Mut(inner), "fin") => {
            return Ok(TypedExpr {
                ty: *inner,
                kind: TypedExprKind::Field {
                    base: Box::new(base),
                    name: name.to_owned(),
                    index: 1,
                },
            });
        }
        (SpecTy::Mut(_), "ptr") => {
            return Ok(TypedExpr {
                ty: ptr_spec_ty(),
                kind: TypedExprKind::Field {
                    base: Box::new(base),
                    name: name.to_owned(),
                    index: 2,
                },
            });
        }
        (SpecTy::Ref(_), _) => {
            return Err(format!("Ref<T> does not have a field named `{name}`"));
        }
        (SpecTy::Mut(_), _) => {
            return Err(format!("Mut<T> does not have a field named `{name}`"));
        }
        _ => {}
    }
    let (struct_name, fields) = match &base.ty {
        SpecTy::Struct {
            name: struct_name, ..
        } => (
            struct_name.clone(),
            struct_fields_for_ty(&base.ty, struct_defs)?
                .ok_or_else(|| format!("unknown spec struct `{struct_name}`"))?,
        ),
        _ => {
            return Err(format!(
                "field access requires a struct, found `{}`",
                display_spec_ty(&base.ty)
            ));
        }
    };
    let Some((index, field_ty)) = fields
        .iter()
        .enumerate()
        .find(|(_, field)| field.name == name)
    else {
        return Err(format!(
            "struct `{struct_name}` does not have a field named `{name}`"
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

fn type_deref_expr(base: TypedExpr) -> Result<TypedExpr, String> {
    match base.ty.clone() {
        SpecTy::Ref(inner) => Ok(TypedExpr {
            ty: *inner,
            kind: TypedExprKind::Field {
                base: Box::new(base),
                name: "deref".to_owned(),
                index: 0,
            },
        }),
        SpecTy::Mut(inner) => Ok(TypedExpr {
            ty: *inner,
            kind: TypedExprKind::Field {
                base: Box::new(base),
                name: "cur".to_owned(),
                index: 0,
            },
        }),
        other => Err(format!(
            "dereference requires Ref<T> or Mut<T>, found `{}`",
            display_spec_ty(&other)
        )),
    }
}

fn type_cast_expr(arg: TypedExpr, ty: &SpecTy) -> Result<TypedExpr, String> {
    if !is_integer_spec_ty(&arg.ty) || !is_integer_spec_ty(ty) {
        return Err(format!(
            "casts require integer types, found `{}` and `{}`",
            display_spec_ty(&arg.ty),
            display_spec_ty(ty)
        ));
    }
    Ok(TypedExpr {
        ty: ty.clone(),
        kind: TypedExprKind::Cast { arg: Box::new(arg) },
    })
}

fn type_tuple_field_expr(base: TypedExpr, index: usize) -> Result<TypedExpr, String> {
    let SpecTy::Tuple(items) = &base.ty else {
        if matches!(base.ty, SpecTy::Struct { .. }) {
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

fn infer_variant_selector_ty(
    base_ty: InferredExprTy,
    enum_name: &str,
    ctor_name: &str,
    type_args: &[SpecTy],
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<InferredExprTy, String> {
    let InferredExprTy::Known(base_ty) = base_ty else {
        return Ok(InferredExprTy::Unknown);
    };
    let SpecTy::Enum {
        name: base_enum_name,
        args,
    } = base_ty
    else {
        return Err(format!(
            "variant selector requires an enum, found `{}`",
            display_spec_ty(&base_ty)
        ));
    };
    if base_enum_name != enum_name {
        return Err(format!(
            "variant selector `{enum_name}::{ctor_name}` does not match enum `{base_enum_name}`"
        ));
    }
    let enum_def = enum_defs
        .get(enum_name)
        .ok_or_else(|| format!("unknown spec enum `{enum_name}`"))?;
    variant_selector_payload_ty(
        enum_def,
        ctor_name,
        type_args,
        &args,
        enum_defs,
        struct_defs,
    )
    .map(InferredExprTy::Known)
}

fn type_variant_selector(
    base: TypedExpr,
    enum_name: &str,
    ctor_name: &str,
    type_args: &[SpecTy],
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<TypedExpr, String> {
    let SpecTy::Enum {
        name: base_enum_name,
        args,
    } = &base.ty
    else {
        return Err(format!(
            "variant selector requires an enum, found `{}`",
            display_spec_ty(&base.ty)
        ));
    };
    if base_enum_name != enum_name {
        return Err(format!(
            "variant selector `{enum_name}::{ctor_name}` does not match enum `{base_enum_name}`"
        ));
    }
    let enum_def = enum_defs
        .get(enum_name)
        .ok_or_else(|| format!("unknown spec enum `{enum_name}`"))?;
    let (ctor_index, ty) =
        variant_selector_payload(enum_def, ctor_name, type_args, args, enum_defs, struct_defs)?;
    Ok(TypedExpr {
        ty,
        kind: TypedExprKind::VariantSelector {
            base: Box::new(base),
            enum_name: enum_name.to_owned(),
            ctor_name: ctor_name.to_owned(),
            ctor_index,
        },
    })
}

fn variant_selector_payload_ty(
    enum_def: &EnumDef,
    ctor_name: &str,
    type_args: &[SpecTy],
    inferred_args: &[SpecTy],
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<SpecTy, String> {
    variant_selector_payload(
        enum_def,
        ctor_name,
        type_args,
        inferred_args,
        enum_defs,
        struct_defs,
    )
    .map(|(_, ty)| ty)
}

fn variant_selector_payload(
    enum_def: &EnumDef,
    ctor_name: &str,
    type_args: &[SpecTy],
    inferred_args: &[SpecTy],
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<(usize, SpecTy), String> {
    let (ctor_index, ctor) = enum_def.ctor(ctor_name).ok_or_else(|| {
        format!(
            "enum `{}` does not define constructor `{ctor_name}`",
            enum_def.name
        )
    })?;
    let func = format!("{}::{ctor_name}", enum_def.name);
    let mut bindings = explicit_enum_type_bindings(&func, enum_def, type_args, enum_defs)?;
    let base_ty = SpecTy::Enum {
        name: enum_def.name.clone(),
        args: inferred_args.to_vec(),
    };
    let _ = seed_enum_type_param_bindings(enum_def, &base_ty, &mut bindings)?;
    let fields = ctor
        .fields
        .iter()
        .map(|field_ty| {
            try_instantiate_spec_ty(field_ty, &bindings).ok_or_else(|| {
                format!(
                    "could not instantiate field type for constructor `{}`",
                    ctor.name
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if !ctor.field_names.is_empty() && ctor.field_names.iter().all(Option::is_some) {
        let name = format!("{}::{}", enum_def.name, ctor.name);
        let Some(struct_def) = struct_defs.get(&name) else {
            return Err(format!("unknown spec struct `{name}`"));
        };
        if struct_def.type_params.len() != enum_def.type_params.len() {
            return Err(format!("spec struct `{name}` does not match enum variant"));
        }
        Ok((
            ctor_index,
            SpecTy::Struct {
                name,
                args: inferred_args.to_vec(),
            },
        ))
    } else {
        Ok((ctor_index, SpecTy::Tuple(fields)))
    }
}

fn compute_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
    ghosts: &RawGlobalGhostPrepass,
) -> Result<DirectivePrepass, LoopPrepassError> {
    let enum_defs = &ghosts.enums;
    let struct_defs = &ghosts.structs;
    let pure_fns = &ghosts.pure_fns;
    let lemma_defs = &ghosts.lemmas;
    let binding_info = collect_hir_binding_info(tcx, def_id)?;
    let hir_locals = compute_hir_locals(tcx, body, &binding_info);
    let directive_type_param_scope = HashSet::new();
    let mut directives =
        collect_function_directives(tcx, def_id, item_span).map_err(directive_error_to_prepass)?;
    let path = tcx.def_path_str(def_id.to_def_id());
    append_standalone_proof_directives(
        tcx,
        def_id,
        item_span,
        body,
        ghosts,
        &path,
        &mut directives,
    )?;
    let unsafe_blocks = collect_unsafe_block_spans(tcx, def_id);
    reject_directives_inside_unsafe_blocks(&directives, &unsafe_blocks)?;
    let mut contract_scope = SpecScope::default();
    let mut req_directive = None;
    let mut ens_directive = None;
    let mut raw_req_directives = Vec::new();
    let mut raw_ens_directives = Vec::new();
    let mut contract_lets = Vec::new();
    for directive in &directives.directives {
        match directive.kind {
            DirectiveKind::Let if matches!(directive.attach, DirectiveAttach::Function) => {
                contract_lets.push(directive);
            }
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
            DirectiveKind::RawReq if matches!(directive.attach, DirectiveAttach::Function) => {
                raw_req_directives.push(directive);
            }
            DirectiveKind::RawEns if matches!(directive.attach, DirectiveAttach::Function) => {
                raw_ens_directives.push(directive);
            }
            _ => {}
        }
    }
    let first_req_line = req_directive
        .map(|directive| directive.line_no)
        .into_iter()
        .chain(raw_req_directives.iter().map(|directive| directive.line_no))
        .min();
    if let Some(req_line) = first_req_line {
        for directive in &contract_lets {
            if directive.line_no > req_line {
                return Err(LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message:
                        "//@ let directives in function contracts must be placed before //@ req or //@ raw req"
                            .to_owned(),
                });
            }
        }
    }
    let has_raw_contract = !raw_req_directives.is_empty() || !raw_ens_directives.is_empty();
    if has_raw_contract && !tcx.fn_sig(def_id).skip_binder().safety().is_unsafe() {
        return Err(LoopPrepassError {
            span: tcx.def_span(def_id.to_def_id()),
            display_span: None,
            message: "raw function contracts are only supported on unsafe functions".to_owned(),
        });
    }
    let param_names = if req_directive.is_some()
        || ens_directive.is_some()
        || has_raw_contract
        || !contract_lets.is_empty()
    {
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
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let param_rust_tys: HashMap<_, _> = param_names
        .iter()
        .cloned()
        .zip(sig.inputs().skip_binder().iter().copied())
        .collect();
    let result_rust_ty = sig.output().skip_binder();
    let result_ty = result.clone();
    for directive in &contract_lets {
        let (name, value) = directive.let_binding().expect("let directive payload");
        validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            value,
            pure_fns,
            enum_defs,
            &directive_type_param_scope,
            &param_names,
            false,
            &mut contract_scope,
        )?;
        contract_scope.bind_let(
            name,
            directive.span,
            Some(directive.span_text.clone()),
            None,
        )?;
    }
    if let Some(directive) = req_directive {
        validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            directive.expr(),
            pure_fns,
            enum_defs,
            &directive_type_param_scope,
            &param_names,
            false,
            &mut contract_scope,
        )?
    }
    for directive in &raw_req_directives {
        validate_function_contract_raw_prepass(
            directive,
            pure_fns,
            enum_defs,
            &directive_type_param_scope,
            &param_names,
            false,
            &mut contract_scope,
        )?;
    }
    let mut body_scope = contract_scope.clone();
    let mut resolved_exprs = HashMap::new();
    for directive in directives.directives.iter().filter(|directive| {
        matches!(
            directive.kind,
            DirectiveKind::Let
                | DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::RawAssert
                | DirectiveKind::Inv
                | DirectiveKind::LemmaCall
        )
    }) {
        if directive.kind == DirectiveKind::Let
            && matches!(directive.attach, DirectiveAttach::Function)
        {
            continue;
        }
        body_scope.prune_expired(directive_anchor_span(&directive.attach));
        let resolution = match directive.kind {
            DirectiveKind::LemmaCall => resolve_lemma_call_expr_env(
                directive.expr(),
                pure_fns,
                enum_defs,
                &directive_type_param_scope,
                &binding_info,
                &hir_locals,
                directive.span,
                directive_anchor_span(&directive.attach),
                lemma_defs,
                &mut body_scope,
            )?,
            DirectiveKind::Let => {
                let (name, value) = directive.let_binding().expect("let directive payload");
                let resolution = resolve_expr_env(
                    value,
                    pure_fns,
                    enum_defs,
                    &binding_info,
                    &hir_locals,
                    directive.span,
                    directive_anchor_span(&directive.attach),
                    directive.kind,
                    &mut body_scope,
                )?;
                body_scope.bind_let(
                    name,
                    directive.span,
                    Some(directive.span_text.clone()),
                    directive.scope_span,
                )?;
                resolution
            }
            DirectiveKind::RawAssert => resolve_raw_pattern_env(
                directive.raw_assertion().expect("raw assertion payload"),
                pure_fns,
                enum_defs,
                &binding_info,
                &hir_locals,
                directive.span,
                directive_anchor_span(&directive.attach),
                &mut body_scope,
            )?,
            _ => resolve_expr_env(
                directive.expr(),
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
            directive.expr(),
            pure_fns,
            enum_defs,
            &directive_type_param_scope,
            &param_names,
            true,
            &mut contract_scope,
        )?
    }
    for directive in &raw_ens_directives {
        validate_function_contract_raw_prepass(
            directive,
            pure_fns,
            enum_defs,
            &directive_type_param_scope,
            &param_names,
            true,
            &mut contract_scope,
        )?;
    }
    let mut inferred = SpecTypeInference::default();
    let mut contract_infer_scope = SpecScope::default();
    for directive in &contract_lets {
        let (name, value) = directive.let_binding().expect("let directive payload");
        let inferred_ty = infer_runtime_contract_expr_types(
            value,
            pure_fns,
            enum_defs,
            struct_defs,
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
        contract_infer_scope.bind_let(
            name,
            directive.span,
            Some(directive.span_text.clone()),
            None,
        )?;
        constrain_let_binding_ty(name, inferred_ty, &mut inferred).map_err(|message| {
            LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message,
            }
        })?;
    }
    if let Some(directive) = req_directive {
        infer_runtime_contract_expr_types(
            directive.expr(),
            pure_fns,
            enum_defs,
            struct_defs,
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
    for directive in &raw_req_directives {
        infer_contract_raw_assertion(
            directive.raw_assertion().expect("raw req payload"),
            pure_fns,
            enum_defs,
            struct_defs,
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
            DirectiveKind::Let
                | DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::RawAssert
                | DirectiveKind::Inv
                | DirectiveKind::LemmaCall
        )
    }) {
        if directive.kind == DirectiveKind::Let
            && matches!(directive.attach, DirectiveAttach::Function)
        {
            continue;
        }
        body_infer_scope.prune_expired(directive_anchor_span(&directive.attach));
        let resolution = resolved_exprs
            .get(&directive.span_text)
            .expect("resolved body expression");
        let local_tys =
            local_spec_tys(tcx, body, resolution).map_err(|message| LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message,
            })?;
        let directive_call_ctx = SpecCallContext::new(
            pure_fns,
            enum_defs,
            struct_defs,
            &directive_type_param_scope,
        );
        match directive.kind {
            DirectiveKind::LemmaCall => {
                infer_lemma_call(
                    directive.expr(),
                    lemma_defs,
                    SpecCallContext {
                        pure_fns,
                        enum_defs,
                        struct_defs,
                        type_param_scope: &directive_type_param_scope,
                    },
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
            DirectiveKind::Let => {
                let (name, value) = directive.let_binding().expect("let directive payload");
                let inferred_ty = infer_body_expr_types(
                    value,
                    directive_call_ctx,
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
                body_infer_scope.bind_let(
                    name,
                    directive.span,
                    Some(directive.span_text.clone()),
                    directive.scope_span,
                )?;
                constrain_let_binding_ty(name, inferred_ty, &mut inferred).map_err(|message| {
                    LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message,
                    }
                })?;
            }
            DirectiveKind::RawAssert => {
                infer_raw_pattern_types(
                    directive.raw_assertion().expect("raw assertion payload"),
                    pure_fns,
                    enum_defs,
                    struct_defs,
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
                    directive.expr(),
                    directive_call_ctx,
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
            directive.expr(),
            pure_fns,
            enum_defs,
            struct_defs,
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
    for directive in &raw_ens_directives {
        infer_contract_raw_assertion(
            directive.raw_assertion().expect("raw ens payload"),
            pure_fns,
            enum_defs,
            struct_defs,
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
    let mut typed_contract_lets = Vec::new();
    let mut contract_type_scope = SpecScope::default();
    for directive in &contract_lets {
        let (name, value) = directive.let_binding().expect("let directive payload");
        let typed = typed_runtime_contract_expr(
            value,
            pure_fns,
            enum_defs,
            struct_defs,
            &mut contract_type_scope,
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
        contract_type_scope.bind_let(
            name,
            directive.span,
            Some(directive.span_text.clone()),
            None,
        )?;
        typed_contract_lets.push(NormalizedBinding {
            name: name.to_owned(),
            value: typed,
        });
    }
    let typed_req = match req_directive {
        Some(directive) => {
            let mut scope = contract_type_scope.clone();
            let typed = typed_runtime_contract_expr(
                directive.expr(),
                pure_fns,
                enum_defs,
                struct_defs,
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
                bind_free_normalized_predicate(typed_contract_lets.clone(), typed, "//@ req")
                    .map_err(|message| LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message,
                    })?,
            )
        }
        None => None,
    };
    let typed_raw_reqs = typed_contract_raw_assertions(
        tcx,
        &raw_req_directives,
        pure_fns,
        enum_defs,
        struct_defs,
        &mut contract_type_scope,
        &param_tys,
        &param_rust_tys,
        false,
        &result_ty,
        result_rust_ty,
        &mut inferred,
    )?;
    let mut typed_body_assertions = HashMap::new();
    let mut typed_body_exprs = HashMap::new();
    let mut typed_body_lets = HashMap::new();
    let mut typed_body_raw_assertions = HashMap::new();
    let mut body_type_scope = if req_directive.is_some() || !contract_lets.is_empty() {
        let mut scope = contract_type_scope.clone();
        if let Some(directive) = req_directive {
            let _ = typed_runtime_contract_expr(
                directive.expr(),
                pure_fns,
                enum_defs,
                struct_defs,
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
            DirectiveKind::Let
                | DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::RawAssert
                | DirectiveKind::Inv
                | DirectiveKind::LemmaCall
        )
    }) {
        if directive.kind == DirectiveKind::Let
            && matches!(directive.attach, DirectiveAttach::Function)
        {
            continue;
        }
        body_type_scope.prune_expired(directive_anchor_span(&directive.attach));
        let resolution = resolved_exprs
            .get(&directive.span_text)
            .expect("resolved body expression");
        let local_tys =
            local_spec_tys(tcx, body, resolution).map_err(|message| LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message,
            })?;
        let directive_call_ctx = SpecCallContext::new(
            pure_fns,
            enum_defs,
            struct_defs,
            &directive_type_param_scope,
        );
        match directive.kind {
            DirectiveKind::LemmaCall => {
                let contract = typed_lemma_call(
                    directive.expr(),
                    &directive.span_text,
                    lemma_defs,
                    SpecCallContext {
                        pure_fns,
                        enum_defs,
                        struct_defs,
                        type_param_scope: &directive_type_param_scope,
                    },
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
            DirectiveKind::Let => {
                let (name, value) = directive.let_binding().expect("let directive payload");
                let typed = typed_body_expr(
                    value,
                    directive_call_ctx,
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
                body_type_scope.bind_let(
                    name,
                    directive.span,
                    Some(directive.span_text.clone()),
                    directive.scope_span,
                )?;
                typed_body_lets.insert(
                    directive.span_text.clone(),
                    NormalizedBinding {
                        name: name.to_owned(),
                        value: typed,
                    },
                );
            }
            DirectiveKind::RawAssert => {
                let resolution = resolved_exprs
                    .get(&directive.span_text)
                    .expect("resolved raw assertion expression");
                let assertion = directive.raw_assertion().expect("raw assertion payload");
                let raw_ctx = RawTypingCtx {
                    tcx,
                    body,
                    resolution,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    local_tys: &local_tys,
                };
                let typed =
                    typed_raw_pattern(assertion, &raw_ctx, &mut body_type_scope, &mut inferred)
                        .map_err(|message| LoopPrepassError {
                            span: directive.span,
                            display_span: Some(directive.span_text.clone()),
                            message,
                        })?;
                typed_body_raw_assertions.insert(directive.span_text.clone(), typed);
                let condition = typed_body_expr_with_expected(
                    &assertion.condition,
                    directive_call_ctx,
                    directive.kind,
                    &mut body_type_scope,
                    &local_tys,
                    &mut inferred,
                    false,
                    Some(&SpecTy::Bool),
                )
                .map_err(|message| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message,
                })?;
                typed_body_exprs.insert(directive.span_text.clone(), condition);
            }
            _ => {
                let typed = typed_body_expr(
                    directive.expr(),
                    directive_call_ctx,
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
                        DirectiveKind::Req
                        | DirectiveKind::Ens
                        | DirectiveKind::Let
                        | DirectiveKind::RawAssert
                        | DirectiveKind::RawReq
                        | DirectiveKind::RawEns
                        | DirectiveKind::LemmaCall => {
                            unreachable!("filtered above")
                        }
                    };
                typed_body_exprs.insert(directive.span_text.clone(), typed);
            }
        }
    }
    let typed_ens = match ens_directive {
        Some(directive) => {
            let mut scope = contract_type_scope.clone();
            if let Some(req) = req_directive {
                let _ = typed_runtime_contract_expr(
                    req.expr(),
                    pure_fns,
                    enum_defs,
                    struct_defs,
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
                directive.expr(),
                pure_fns,
                enum_defs,
                struct_defs,
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
    let typed_raw_ens = typed_contract_raw_assertions(
        tcx,
        &raw_ens_directives,
        pure_fns,
        enum_defs,
        struct_defs,
        &mut contract_type_scope,
        &param_tys,
        &param_rust_tys,
        true,
        &result_ty,
        result_rust_ty,
        &mut inferred,
    )?;
    let explicit_function_contract = req_directive.is_some()
        || ens_directive.is_some()
        || !raw_req_directives.is_empty()
        || !raw_ens_directives.is_empty()
        || !contract_lets.is_empty();
    let function_contract = match (
        req_directive,
        ens_directive,
        typed_raw_reqs.is_empty(),
        typed_raw_ens.is_empty(),
    ) {
        (None, None, true, true) if !contract_lets.is_empty() => {
            return Err(LoopPrepassError {
                span: tcx.def_span(def_id.to_def_id()),
                display_span: None,
                message:
                    "function contract requires a //@ req, //@ ens, //@ raw req, or //@ raw ens predicate"
                        .to_owned(),
            });
        }
        (req, ens, _, _) => Some(FunctionContract {
            params: params.clone(),
            req: typed_req.unwrap_or_else(|| NormalizedPredicate {
                bindings: typed_contract_lets,
                condition: typed_bool_expr(true),
            }),
            req_span: req
                .map(|directive| directive.span_text.clone())
                .unwrap_or_else(|| def_span.clone()),
            raw_reqs: typed_raw_reqs,
            ens: typed_ens.unwrap_or_else(|| typed_bool_expr(true)),
            ens_span: ens
                .map(|directive| directive.span_text.clone())
                .unwrap_or(def_span),
            raw_ens: typed_raw_ens,
            result,
        }),
    };
    let loop_contracts =
        collect_loop_contracts(tcx, body, &directives, &resolved_exprs, &typed_body_exprs)?;
    let mut control_point_directives = ControlPointDirectives::default();

    for directive in directives.directives {
        match directive.kind {
            DirectiveKind::Req
            | DirectiveKind::Ens
            | DirectiveKind::RawReq
            | DirectiveKind::RawEns => {}
            DirectiveKind::Let if matches!(directive.attach, DirectiveAttach::Function) => {}
            DirectiveKind::Let => {
                let control = control_point_after(body, directive_anchor_span(&directive.attach))
                    .ok_or_else(|| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message: format!(
                        "unable to map //@ let at {} to MIR",
                        tcx.sess
                            .source_map()
                            .span_to_diagnostic_string(directive.span)
                    ),
                })?;
                let resolution = resolved_exprs
                    .get(&directive.span_text)
                    .cloned()
                    .expect("resolved let expression");
                control_point_directives
                    .by_control_point
                    .entry(control)
                    .or_default()
                    .push(ControlPointDirective::Let(LetBindingContract {
                        binding: typed_body_lets
                            .get(&directive.span_text)
                            .cloned()
                            .expect("typed let expression"),
                        resolution,
                    }));
            }
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
            DirectiveKind::RawAssert => {
                let control = control_point_after(body, directive_anchor_span(&directive.attach))
                    .ok_or_else(|| LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message: format!(
                        "unable to map //@ raw assert at {} to MIR",
                        tcx.sess
                            .source_map()
                            .span_to_diagnostic_string(directive.span)
                    ),
                })?;
                let resolution = resolved_exprs
                    .get(&directive.span_text)
                    .cloned()
                    .expect("resolved raw assertion expression");
                control_point_directives
                    .by_control_point
                    .entry(control)
                    .or_default()
                    .push(ControlPointDirective::RawAssert(Box::new(
                        RawAssertionContract {
                            pattern: typed_body_raw_assertions
                                .get(&directive.span_text)
                                .cloned()
                                .expect("typed raw assertion expression"),
                            condition: typed_body_exprs
                                .get(&directive.span_text)
                                .cloned()
                                .expect("typed raw assertion condition"),
                            resolution,
                            assertion_span: directive.span_text.clone(),
                        },
                    )));
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
        explicit_function_contract,
        function_contract,
        unsafe_blocks,
    })
}

fn append_standalone_proof_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
    ghosts: &RawGlobalGhostPrepass,
    path: &str,
    directives: &mut CollectedFunctionDirectives,
) -> Result<(), LoopPrepassError> {
    let Some(def) = ghosts.standalone_fn_contracts.get(path) else {
        return Ok(());
    };
    if def.proof_blocks.is_empty() {
        return Ok(());
    }
    if directives.directives.iter().any(|directive| {
        !matches!(
            directive.kind,
            DirectiveKind::Req | DirectiveKind::Ens | DirectiveKind::RawReq | DirectiveKind::RawEns
        ) && !matches!(
            (directive.kind, &directive.attach),
            (DirectiveKind::Let, DirectiveAttach::Function)
        )
    }) {
        return Err(LoopPrepassError {
            span: item_span,
            display_span: None,
            message: "inline body directives cannot be mixed with standalone proof directives"
                .to_owned(),
        });
    }

    let anchors =
        collect_function_directive_anchors(tcx, def_id).map_err(directive_error_to_prepass)?;
    let exits = function_exit_spans(body);
    for proof_block in &def.proof_blocks {
        let (attach, scope_span) = match proof_block.anchor {
            StandaloneProofAnchor::Stmt(index) => {
                let anchor = anchors
                    .statements
                    .get(index)
                    .ok_or_else(|| LoopPrepassError {
                        span: item_span,
                        display_span: None,
                        message: format!(
                            "standalone proof anchor `at stmt #{index}` does not exist in `{path}`"
                        ),
                    })?;
                (
                    DirectiveAttach::Statement {
                        anchor_span: anchor.span,
                    },
                    anchor.scope_span,
                )
            }
            StandaloneProofAnchor::Loop(index) => {
                let anchor = anchors.loops.get(index).ok_or_else(|| LoopPrepassError {
                    span: item_span,
                    display_span: None,
                    message: format!(
                        "standalone proof anchor `at loop #{index}` does not exist in `{path}`"
                    ),
                })?;
                if proof_block.directives.len() != 1
                    || proof_block.directives[0].kind != StandaloneProofDirectiveKind::Inv
                {
                    return Err(LoopPrepassError {
                        span: item_span,
                        display_span: None,
                        message:
                            "standalone proof `at loop` blocks must contain exactly one `inv` directive"
                                .to_owned(),
                    });
                }
                (
                    DirectiveAttach::Loop {
                        loop_expr_id: anchor.loop_expr_id,
                        loop_span: anchor.loop_span,
                        body_span: anchor.body_span,
                        entry_span: anchor.entry_span,
                    },
                    None,
                )
            }
            StandaloneProofAnchor::Exit(index) => {
                let span = exits.get(index).copied().ok_or_else(|| LoopPrepassError {
                    span: item_span,
                    display_span: None,
                    message: format!(
                        "standalone proof anchor `at exit #{index}` does not exist in `{path}`"
                    ),
                })?;
                (DirectiveAttach::Statement { anchor_span: span }, None)
            }
        };
        for (directive_index, proof_directive) in proof_block.directives.iter().enumerate() {
            if matches!(
                proof_block.anchor,
                StandaloneProofAnchor::Stmt(_) | StandaloneProofAnchor::Exit(_)
            ) && proof_directive.kind == StandaloneProofDirectiveKind::Inv
            {
                return Err(LoopPrepassError {
                    span: item_span,
                    display_span: None,
                    message: "`inv` directives are only supported in `at loop` proof blocks"
                        .to_owned(),
                });
            }
            let kind = match proof_directive.kind {
                StandaloneProofDirectiveKind::Let => DirectiveKind::Let,
                StandaloneProofDirectiveKind::Inv => DirectiveKind::Inv,
                StandaloneProofDirectiveKind::Assert => DirectiveKind::Assert,
                StandaloneProofDirectiveKind::Assume => DirectiveKind::Assume,
                StandaloneProofDirectiveKind::RawAssert => DirectiveKind::RawAssert,
                StandaloneProofDirectiveKind::LemmaCall => DirectiveKind::LemmaCall,
            };
            let payload = match &proof_directive.payload {
                StandaloneProofPayload::Predicate(expr) => {
                    crate::directive::DirectivePayload::Predicate(expr.clone())
                }
                StandaloneProofPayload::Let { name, value } => {
                    crate::directive::DirectivePayload::Let {
                        name: name.clone(),
                        value: value.clone(),
                    }
                }
                StandaloneProofPayload::RawAssert(assertion) => {
                    crate::directive::DirectivePayload::RawAssert(assertion.clone())
                }
                StandaloneProofPayload::LemmaCall(expr) => {
                    crate::directive::DirectivePayload::LemmaCall(expr.clone())
                }
            };
            let origin = DirectiveOrigin::Standalone {
                path: path.to_owned(),
                anchor: proof_block.anchor.clone(),
                directive_index,
            };
            let line_no = origin.sort_key();
            let span_text = origin.display();
            directives.directives.push(FunctionDirective {
                kind,
                span: item_span,
                span_text,
                line_no,
                origin,
                attach: attach.clone(),
                payload,
                scope_span,
            });
        }
    }
    directives
        .directives
        .sort_by_key(|directive| directive.origin.sort_key());
    Ok(())
}

fn function_exit_spans(body: &Body<'_>) -> Vec<Span> {
    body.basic_blocks
        .iter()
        .filter_map(|data| {
            let terminator = data.terminator();
            matches!(terminator.kind, TerminatorKind::Return).then_some(terminator.source_info.span)
        })
        .collect()
}

fn collect_unsafe_block_spans<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Vec<Span> {
    let hir_body = tcx.hir_body_owned_by(def_id);
    let mut collector = UnsafeBlockCollector { spans: Vec::new() };
    collector.visit_expr(hir_body.value);
    collector.spans
}

#[allow(clippy::too_many_arguments)]
fn resolve_raw_pattern_env(
    assertion: &RawAssertion,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    spec_scope: &mut SpecScope,
) -> Result<ResolvedExprEnv, LoopPrepassError> {
    let mut resolved = ResolvedExprEnv::default();
    resolve_raw_pattern_env_into(
        &assertion.pattern,
        pure_fns,
        enum_defs,
        binding_info,
        hir_locals,
        span,
        anchor_span,
        spec_scope,
        &mut resolved,
    )?;
    let condition_resolved = resolve_expr_env(
        &assertion.condition,
        pure_fns,
        enum_defs,
        binding_info,
        hir_locals,
        span,
        anchor_span,
        DirectiveKind::RawAssert,
        spec_scope,
    )?;
    resolved.locals.extend(condition_resolved.locals);
    Ok(resolved)
}

#[allow(clippy::too_many_arguments)]
fn resolve_raw_pattern_env_into(
    pattern: &RawPattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    spec_scope: &mut SpecScope,
    resolved: &mut ResolvedExprEnv,
) -> Result<(), LoopPrepassError> {
    match pattern {
        RawPattern::Emp => Ok(()),
        RawPattern::Star(lhs, rhs) => {
            resolve_raw_pattern_env_into(
                lhs,
                pure_fns,
                enum_defs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                spec_scope,
                resolved,
            )?;
            resolve_raw_pattern_env_into(
                rhs,
                pure_fns,
                enum_defs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                spec_scope,
                resolved,
            )
        }
        RawPattern::PointsTo { addr, ty, value } => {
            for expr in [addr, ty] {
                let expr_resolved = resolve_expr_env(
                    expr,
                    pure_fns,
                    enum_defs,
                    binding_info,
                    hir_locals,
                    span,
                    anchor_span,
                    DirectiveKind::RawAssert,
                    spec_scope,
                )?;
                resolved.locals.extend(expr_resolved.locals);
            }
            resolve_value_pattern_env(
                value,
                pure_fns,
                enum_defs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                spec_scope,
                resolved,
            )?;
            Ok(())
        }
        RawPattern::PointsToSugar { pointer, value } => {
            let symbol = Symbol::intern(pointer);
            let Some(hir_id) = resolve_binding_hir_id(binding_info, symbol, anchor_span) else {
                return Err(LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!("unresolved pointer `{pointer}` in //@ raw assert"),
                });
            };
            let Some(local) = hir_locals.get(&hir_id).copied() else {
                return Err(LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!("missing MIR local for pointer `{pointer}`"),
                });
            };
            resolved.locals.insert(pointer.clone(), local);
            resolve_value_pattern_env(
                value,
                pure_fns,
                enum_defs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                spec_scope,
                resolved,
            )?;
            Ok(())
        }
        RawPattern::Own { value, .. } => {
            resolve_value_pattern_env(
                value,
                pure_fns,
                enum_defs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                spec_scope,
                resolved,
            )?;
            Ok(())
        }
        RawPattern::DeallocToken { base, layout } => {
            for expr in [base, layout] {
                let expr_resolved = resolve_expr_env(
                    expr,
                    pure_fns,
                    enum_defs,
                    binding_info,
                    hir_locals,
                    span,
                    anchor_span,
                    DirectiveKind::RawAssert,
                    spec_scope,
                )?;
                resolved.locals.extend(expr_resolved.locals);
            }
            Ok(())
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_value_pattern_env(
    pattern: &ValuePattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    spec_scope: &mut SpecScope,
    resolved: &mut ResolvedExprEnv,
) -> Result<(), LoopPrepassError> {
    match pattern {
        ValuePattern::Bind(name) => {
            spec_scope.bind_let(name, span, None, None)?;
            Ok(())
        }
        ValuePattern::Expr(expr) => {
            let expr_resolved = resolve_expr_env(
                expr,
                pure_fns,
                enum_defs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                DirectiveKind::RawAssert,
                spec_scope,
            )?;
            resolved.locals.extend(expr_resolved.locals);
            Ok(())
        }
        ValuePattern::SeqLit(items) => {
            for item in items {
                resolve_value_pattern_env(
                    item,
                    pure_fns,
                    enum_defs,
                    binding_info,
                    hir_locals,
                    span,
                    anchor_span,
                    spec_scope,
                    resolved,
                )?;
            }
            Ok(())
        }
        ValuePattern::StructLit { fields, .. } => {
            for field in fields {
                resolve_value_pattern_env(
                    &field.value,
                    pure_fns,
                    enum_defs,
                    binding_info,
                    hir_locals,
                    span,
                    anchor_span,
                    spec_scope,
                    resolved,
                )?;
            }
            Ok(())
        }
        ValuePattern::Call { args, .. } => {
            for arg in args {
                resolve_value_pattern_env(
                    arg,
                    pure_fns,
                    enum_defs,
                    binding_info,
                    hir_locals,
                    span,
                    anchor_span,
                    spec_scope,
                    resolved,
                )?;
            }
            Ok(())
        }
    }
}

fn infer_raw_pattern_types(
    assertion: &RawAssertion,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    let type_param_scope = HashSet::new();
    let call_ctx = SpecCallContext::new(pure_fns, enum_defs, struct_defs, &type_param_scope);
    infer_raw_pattern_types_into(
        &assertion.pattern,
        call_ctx,
        spec_scope,
        local_tys,
        inferred,
    )?;
    let condition_ty = infer_body_expr_types(
        &assertion.condition,
        call_ctx,
        DirectiveKind::RawAssert,
        spec_scope,
        local_tys,
        inferred,
    )?;
    if let InferredExprTy::Known(ty) = condition_ty {
        let _ = unify_spec_tys(&ty, &SpecTy::Bool)?;
    }
    Ok(())
}

fn infer_raw_pattern_types_into(
    pattern: &RawPattern,
    call_ctx: SpecCallContext<'_>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    match pattern {
        RawPattern::Emp => Ok(()),
        RawPattern::Star(lhs, rhs) => {
            infer_raw_pattern_types_into(lhs, call_ctx, spec_scope, local_tys, inferred)?;
            infer_raw_pattern_types_into(rhs, call_ctx, spec_scope, local_tys, inferred)
        }
        RawPattern::PointsTo { addr, ty, value } => {
            for expr in [addr, ty] {
                infer_body_expr_types(
                    expr,
                    call_ctx,
                    DirectiveKind::RawAssert,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            if value_pattern_contains_bind(value) {
                let ty_ty = typed_raw_expr(ty, call_ctx, spec_scope, local_tys, inferred)?;
                let expected = option_spec_ty_for_rust_ty_expr(&ty_ty, &HashSet::new())?;
                infer_value_pattern_types(
                    value, &expected, call_ctx, spec_scope, local_tys, inferred,
                )?;
            } else if let ValuePattern::Expr(expr) = value {
                infer_body_expr_types(
                    expr,
                    call_ctx,
                    DirectiveKind::RawAssert,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            Ok(())
        }
        RawPattern::PointsToSugar { value, .. } => {
            if value_pattern_contains_bind(value) {
                bind_value_pattern_vars(value, spec_scope, inferred)?;
                return Ok(());
            }
            if let ValuePattern::Expr(expr) = value {
                infer_body_expr_types(
                    expr,
                    call_ctx,
                    DirectiveKind::RawAssert,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            Ok(())
        }
        RawPattern::Own { ty, value } => {
            if value_pattern_contains_bind(value) {
                let ty = resolve_own_rust_type_expr(
                    ty,
                    call_ctx.struct_defs,
                    call_ctx.type_param_scope,
                )?;
                infer_value_pattern_types(value, &ty, call_ctx, spec_scope, local_tys, inferred)?;
            } else if let ValuePattern::Expr(expr) = value {
                infer_body_expr_types(
                    expr,
                    call_ctx,
                    DirectiveKind::RawAssert,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            Ok(())
        }
        RawPattern::DeallocToken { base, layout } => {
            for expr in [base, layout] {
                infer_body_expr_types(
                    expr,
                    call_ctx,
                    DirectiveKind::RawAssert,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            Ok(())
        }
    }
}

fn typed_raw_pattern(
    assertion: &RawAssertion,
    ctx: &RawTypingCtx<'_, '_>,
    spec_scope: &mut SpecScope,
    inferred: &mut SpecTypeInference,
) -> Result<TypedRawPattern, String> {
    typed_raw_pattern_into(&assertion.pattern, ctx, spec_scope, inferred)
}

#[allow(clippy::too_many_arguments)]
fn typed_contract_raw_assertions<'tcx>(
    tcx: TyCtxt<'tcx>,
    directives: &[&FunctionDirective],
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    rust_params: &HashMap<String, Ty<'tcx>>,
    allow_result: bool,
    result_ty: &SpecTy,
    result_rust_ty: Ty<'tcx>,
    inferred: &mut SpecTypeInference,
) -> Result<Vec<RawAssertionContract>, LoopPrepassError> {
    let mut out = Vec::with_capacity(directives.len());
    for directive in directives {
        let assertion = directive.raw_assertion().expect("raw contract payload");
        let pattern = typed_contract_raw_pattern(
            tcx,
            &assertion.pattern,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            rust_params,
            allow_result,
            result_ty,
            result_rust_ty,
            inferred,
        )
        .map_err(|message| LoopPrepassError {
            span: directive.span,
            display_span: Some(directive.span_text.clone()),
            message,
        })?;
        let condition = typed_contract_expr_with_expected(
            &assertion.condition,
            pure_fns,
            enum_defs,
            struct_defs,
            &HashSet::new(),
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            true,
            Some(&SpecTy::Bool),
        )
        .map_err(|message| LoopPrepassError {
            span: directive.span,
            display_span: Some(directive.span_text.clone()),
            message,
        })?;
        out.push(RawAssertionContract {
            pattern,
            condition,
            resolution: ResolvedExprEnv::default(),
            assertion_span: directive.span_text.clone(),
        });
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn typed_lemma_raw_assertions(
    assertions: &[RawAssertion],
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<Vec<RawAssertionContract>, String> {
    let mut out = Vec::with_capacity(assertions.len());
    for assertion in assertions {
        let pattern = typed_lemma_raw_pattern(
            &assertion.pattern,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
        )?;
        let condition = typed_contract_expr_with_expected(
            &assertion.condition,
            pure_fns,
            enum_defs,
            struct_defs,
            &HashSet::new(),
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            true,
            Some(&SpecTy::Bool),
        )?;
        out.push(RawAssertionContract {
            pattern,
            condition,
            resolution: ResolvedExprEnv::default(),
            assertion_span: "lemma raw contract".to_owned(),
        });
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn typed_lemma_raw_pattern(
    pattern: &RawPattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<TypedRawPattern, String> {
    match pattern {
        RawPattern::Emp => Ok(TypedRawPattern::Emp),
        RawPattern::Star(lhs, rhs) => Ok(TypedRawPattern::Star(
            Box::new(typed_lemma_raw_pattern(
                lhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?),
            Box::new(typed_lemma_raw_pattern(
                rhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?),
        )),
        RawPattern::PointsTo { addr, ty, value } => {
            let addr = typed_contract_raw_expr(
                addr,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&SpecTy::Usize),
            )?;
            let ty = typed_contract_raw_expr(
                ty,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&SpecTy::RustTy),
            )?;
            let type_params = contract_type_param_scope(params, result_ty);
            let expected = option_spec_ty_for_rust_ty_expr(&ty, &type_params)?;
            let value = typed_contract_value_pattern(
                value,
                &expected,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            Ok(TypedRawPattern::PointsTo { addr, ty, value })
        }
        RawPattern::PointsToSugar { .. } => {
            Err("`|-?->` raw sugar in unsafe lemmas is unsupported; use `PointsTo(...)`".to_owned())
        }
        RawPattern::Own { ty, value } => {
            let type_params = contract_type_param_scope(params, result_ty);
            let ty = resolve_own_rust_type_expr(ty, struct_defs, &type_params)?;
            let value = typed_contract_value_pattern(
                value,
                &ty,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            Ok(TypedRawPattern::Own { ty, value })
        }
        RawPattern::DeallocToken { base, layout } => Ok(TypedRawPattern::DeallocToken {
            base: typed_contract_raw_expr(
                base,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&SpecTy::Usize),
            )?,
            layout: typed_contract_raw_expr(
                layout,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&layout_spec_ty()),
            )?,
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn typed_contract_raw_pattern<'tcx>(
    tcx: TyCtxt<'tcx>,
    pattern: &RawPattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    rust_params: &HashMap<String, Ty<'tcx>>,
    allow_result: bool,
    result_ty: &SpecTy,
    result_rust_ty: Ty<'tcx>,
    inferred: &mut SpecTypeInference,
) -> Result<TypedRawPattern, String> {
    match pattern {
        RawPattern::Emp => Ok(TypedRawPattern::Emp),
        RawPattern::Star(lhs, rhs) => Ok(TypedRawPattern::Star(
            Box::new(typed_contract_raw_pattern(
                tcx,
                lhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                rust_params,
                allow_result,
                result_ty,
                result_rust_ty,
                inferred,
            )?),
            Box::new(typed_contract_raw_pattern(
                tcx,
                rhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                rust_params,
                allow_result,
                result_ty,
                result_rust_ty,
                inferred,
            )?),
        )),
        RawPattern::PointsTo { addr, ty, value } => {
            let addr = typed_contract_raw_expr(
                addr,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&SpecTy::Usize),
            )?;
            let ty = typed_contract_raw_expr(
                ty,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&SpecTy::RustTy),
            )?;
            let type_params = contract_type_param_scope(params, result_ty);
            let expected = option_spec_ty_for_rust_ty_expr(&ty, &type_params)?;
            let value = typed_contract_value_pattern(
                value,
                &expected,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            Ok(TypedRawPattern::PointsTo { addr, ty, value })
        }
        RawPattern::PointsToSugar { pointer, value } => {
            let pointer_ty = if allow_result && pointer == "result" {
                result_rust_ty
            } else {
                *rust_params
                    .get(pointer)
                    .ok_or_else(|| format!("unresolved pointer `{pointer}` in raw contract"))?
            };
            let pointee_rust_ty = match pointer_ty.kind() {
                TyKind::RawPtr(pointee, _) => *pointee,
                _ => {
                    return Err(format!(
                        "`|-?->` raw pattern requires a raw pointer, found `{}`",
                        display_spec_ty(&spec_ty_for_rust_ty(tcx, pointer_ty)?)
                    ));
                }
            };
            let pointee_ty = spec_ty_for_rust_ty(tcx, pointee_rust_ty)?;
            let addr = TypedExpr {
                ty: SpecTy::Usize,
                kind: TypedExprKind::Field {
                    base: Box::new(TypedExpr {
                        ty: ptr_spec_ty(),
                        kind: if allow_result && pointer == "result" {
                            TypedExprKind::Var(pointer.clone())
                        } else {
                            TypedExprKind::RustVar(pointer.clone())
                        },
                    }),
                    name: "addr".to_owned(),
                    index: 0,
                },
            };
            let ty = TypedExpr {
                ty: SpecTy::RustTy,
                kind: TypedExprKind::RustType(RustTyKey::new(rust_ty_key_text_for_rust_ty(
                    tcx,
                    pointee_rust_ty,
                )?)),
            };
            let expected = option_spec_ty(pointee_ty);
            let value = typed_contract_value_pattern(
                value,
                &expected,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            Ok(TypedRawPattern::PointsTo { addr, ty, value })
        }
        RawPattern::Own { ty, value } => {
            let type_params = contract_type_param_scope(params, result_ty);
            let ty = resolve_own_rust_type_expr(ty, struct_defs, &type_params)?;
            let value = typed_contract_value_pattern(
                value,
                &ty,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            Ok(TypedRawPattern::Own { ty, value })
        }
        RawPattern::DeallocToken { base, layout } => Ok(TypedRawPattern::DeallocToken {
            base: typed_contract_raw_expr(
                base,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&SpecTy::Usize),
            )?,
            layout: typed_contract_raw_expr(
                layout,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                Some(&layout_spec_ty()),
            )?,
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn typed_contract_raw_expr(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
    expected: Option<&SpecTy>,
) -> Result<TypedExpr, String> {
    typed_contract_expr_with_expected(
        expr,
        pure_fns,
        enum_defs,
        struct_defs,
        &HashSet::new(),
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        true,
        expected,
    )
}

#[allow(clippy::too_many_arguments)]
fn typed_contract_value_pattern(
    pattern: &ValuePattern,
    expected: &SpecTy,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<TypedValuePattern, String> {
    match pattern {
        ValuePattern::Bind(name) => {
            spec_scope
                .bind_let(name, DUMMY_SP, None, None)
                .map_err(|err| err.message)?;
            inferred.constrain(name, expected)?;
            Ok(TypedValuePattern::Bind {
                name: name.clone(),
                ty: expected.clone(),
            })
        }
        ValuePattern::Expr(expr) => Ok(TypedValuePattern::Expr(typed_contract_raw_expr(
            expr,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            Some(expected),
        )?)),
        ValuePattern::SeqLit(items) => {
            let SpecTy::Seq(inner) = expected else {
                return Err(format!(
                    "sequence raw pattern requires `Seq<T>`, got {}",
                    display_spec_ty(expected)
                ));
            };
            let mut typed_items = Vec::with_capacity(items.len());
            for item in items {
                typed_items.push(typed_contract_value_pattern(
                    item,
                    inner,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                )?);
            }
            Ok(TypedValuePattern::SeqLit {
                ty: expected.clone(),
                items: typed_items,
            })
        }
        ValuePattern::StructLit { name, fields } => {
            let struct_fields = raw_pattern_struct_fields(expected, name, struct_defs)?;
            let mut typed_fields = Vec::with_capacity(fields.len());
            for field in fields {
                let field_ty = struct_fields
                    .iter()
                    .find(|item| item.name == field.name)
                    .ok_or_else(|| format!("unknown field `{}` in `{name}`", field.name))?;
                typed_fields.push(typed_contract_value_pattern(
                    &field.value,
                    &field_ty.ty,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                )?);
            }
            Ok(TypedValuePattern::StructLit {
                ty: expected.clone(),
                fields: typed_fields,
            })
        }
        ValuePattern::Call {
            func,
            type_args,
            args,
        } => {
            let (enum_def, ctor_index) = lookup_enum_ctor(enum_defs, func)
                .ok_or_else(|| format!("unknown constructor `{func}`"))?;
            let mut bindings = explicit_enum_type_bindings(func, enum_def, type_args, enum_defs)?;
            let _ = seed_enum_type_param_bindings(enum_def, expected, &mut bindings)?;
            let (_, ctor) = enum_def
                .ctor(func.rsplit("::").next().unwrap_or(func))
                .ok_or_else(|| format!("unknown constructor `{func}`"))?;
            if ctor.fields.len() != args.len() {
                return Err(format!(
                    "constructor `{func}` expects {} arguments, found {}",
                    ctor.fields.len(),
                    args.len()
                ));
            }
            let ctor_result_ty = instantiate_enum_result_ty(func, enum_def, &bindings)?;
            let _ = unify_spec_tys(&ctor_result_ty, expected)?;
            let mut typed_args = Vec::with_capacity(args.len());
            for (arg, field_ty) in args.iter().zip(&ctor.fields) {
                let expected_field_ty = try_instantiate_spec_ty(field_ty, &bindings)
                    .ok_or_else(|| format!("could not resolve constructor `{func}` field type"))?;
                typed_args.push(typed_contract_value_pattern(
                    arg,
                    &expected_field_ty,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                )?);
            }
            Ok(TypedValuePattern::CtorCall {
                ty: expected.clone(),
                ctor_index,
                args: typed_args,
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn infer_contract_raw_assertion(
    assertion: &RawAssertion,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    infer_contract_raw_pattern_types(
        &assertion.pattern,
        pure_fns,
        enum_defs,
        struct_defs,
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
    )?;
    infer_contract_expr_types_with_expected(
        &assertion.condition,
        pure_fns,
        enum_defs,
        struct_defs,
        &HashSet::new(),
        spec_scope,
        params,
        allow_result,
        result_ty,
        inferred,
        true,
        Some(&SpecTy::Bool),
    )?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn infer_contract_raw_pattern_types(
    pattern: &RawPattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    match pattern {
        RawPattern::Emp => Ok(()),
        RawPattern::Star(lhs, rhs) => {
            infer_contract_raw_pattern_types(
                lhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            infer_contract_raw_pattern_types(
                rhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )
        }
        RawPattern::PointsTo { addr, ty, value } => {
            for (expr, expected) in [(addr, &SpecTy::Usize), (ty, &SpecTy::RustTy)] {
                infer_contract_expr_types_with_expected(
                    expr,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    &HashSet::new(),
                    spec_scope,
                    params,
                    allow_result,
                    result_ty,
                    inferred,
                    true,
                    Some(expected),
                )?;
            }
            infer_contract_value_pattern(
                value,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )
        }
        RawPattern::PointsToSugar { value, .. } => infer_contract_value_pattern(
            value,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
        ),
        RawPattern::Own { value, .. } => infer_contract_value_pattern(
            value,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
        ),
        RawPattern::DeallocToken { base, layout } => {
            infer_contract_expr_types_with_expected(
                base,
                pure_fns,
                enum_defs,
                struct_defs,
                &HashSet::new(),
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                true,
                Some(&SpecTy::Usize),
            )?;
            infer_contract_expr_types_with_expected(
                layout,
                pure_fns,
                enum_defs,
                struct_defs,
                &HashSet::new(),
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
                true,
                Some(&layout_spec_ty()),
            )?;
            Ok(())
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn infer_contract_value_pattern(
    pattern: &ValuePattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    if value_pattern_contains_bind(pattern) {
        bind_value_pattern_vars(pattern, spec_scope, inferred)
    } else if let ValuePattern::Expr(expr) = pattern {
        infer_contract_expr_types_with_expected(
            expr,
            pure_fns,
            enum_defs,
            struct_defs,
            &HashSet::new(),
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            true,
            None,
        )?;
        Ok(())
    } else {
        Ok(())
    }
}

fn typed_raw_pattern_into(
    pattern: &RawPattern,
    ctx: &RawTypingCtx<'_, '_>,
    spec_scope: &mut SpecScope,
    inferred: &mut SpecTypeInference,
) -> Result<TypedRawPattern, String> {
    let type_param_scope = HashSet::new();
    let call_ctx = ctx.call_ctx(&type_param_scope);
    match pattern {
        RawPattern::Emp => Ok(TypedRawPattern::Emp),
        RawPattern::Star(lhs, rhs) => Ok(TypedRawPattern::Star(
            Box::new(typed_raw_pattern_into(lhs, ctx, spec_scope, inferred)?),
            Box::new(typed_raw_pattern_into(rhs, ctx, spec_scope, inferred)?),
        )),
        RawPattern::PointsTo { addr, ty, value } => {
            let addr = typed_raw_expr(addr, call_ctx, spec_scope, ctx.local_tys, inferred)?;
            ensure_raw_expr_ty(&addr, &SpecTy::Usize, "PointsTo address")?;
            let ty = typed_raw_expr(ty, call_ctx, spec_scope, ctx.local_tys, inferred)?;
            ensure_raw_expr_ty(&ty, &SpecTy::RustTy, "PointsTo type")?;
            let value = if value_pattern_contains_bind(value) {
                let expected = option_spec_ty_for_rust_ty_expr(&ty, &HashSet::new())?;
                typed_value_pattern(
                    value,
                    &expected,
                    call_ctx,
                    spec_scope,
                    ctx.local_tys,
                    inferred,
                )?
            } else if let ValuePattern::Expr(expr) = value {
                let typed = typed_raw_expr(expr, call_ctx, spec_scope, ctx.local_tys, inferred)?;
                ensure_option_raw_value(&typed)?;
                TypedValuePattern::Expr(typed)
            } else {
                unreachable!("pattern without binders must be an expression")
            };
            Ok(TypedRawPattern::PointsTo { addr, ty, value })
        }
        RawPattern::PointsToSugar { pointer, value } => {
            let local = *ctx
                .resolution
                .locals
                .get(pointer)
                .ok_or_else(|| format!("unresolved pointer `{pointer}` in //@ raw assert"))?;
            let pointer_ty = ctx.body.local_decls[local].ty;
            let pointee_ty = match pointer_ty.kind() {
                TyKind::RawPtr(pointee, _) => *pointee,
                _ => {
                    return Err(format!(
                        "`|-?->` raw pattern requires a raw pointer, found `{}`",
                        display_spec_ty(&spec_ty_for_rust_ty(ctx.tcx, pointer_ty)?)
                    ));
                }
            };
            let ptr_ty = ptr_spec_ty();
            let addr = TypedExpr {
                ty: SpecTy::Usize,
                kind: TypedExprKind::Field {
                    base: Box::new(TypedExpr {
                        ty: ptr_ty,
                        kind: TypedExprKind::RustVar(pointer.clone()),
                    }),
                    name: "addr".to_owned(),
                    index: 0,
                },
            };
            let ty = TypedExpr {
                ty: SpecTy::RustTy,
                kind: TypedExprKind::RustType(RustTyKey::new(rust_ty_key_text_for_rust_ty(
                    ctx.tcx, pointee_ty,
                )?)),
            };
            let expected = option_spec_ty(spec_ty_for_rust_ty(ctx.tcx, pointee_ty)?);
            let value = if value_pattern_contains_bind(value) {
                typed_value_pattern(
                    value,
                    &expected,
                    call_ctx,
                    spec_scope,
                    ctx.local_tys,
                    inferred,
                )?
            } else if let ValuePattern::Expr(expr) = value {
                let typed = typed_body_expr_with_expected(
                    expr,
                    call_ctx,
                    DirectiveKind::RawAssert,
                    spec_scope,
                    ctx.local_tys,
                    inferred,
                    false,
                    Some(&expected),
                )?;
                ensure_option_raw_value(&typed)?;
                TypedValuePattern::Expr(typed)
            } else {
                unreachable!("pattern without binders must be an expression")
            };
            Ok(TypedRawPattern::PointsTo { addr, ty, value })
        }
        RawPattern::Own { ty, value } => {
            let ty = resolve_own_rust_type_expr(ty, ctx.struct_defs, call_ctx.type_param_scope)?;
            let value =
                typed_value_pattern(value, &ty, call_ctx, spec_scope, ctx.local_tys, inferred)?;
            Ok(TypedRawPattern::Own { ty, value })
        }
        RawPattern::DeallocToken { base, layout } => {
            let base = typed_raw_expr(base, call_ctx, spec_scope, ctx.local_tys, inferred)?;
            ensure_raw_expr_ty(&base, &SpecTy::Usize, "DeallocToken base")?;
            let layout = typed_raw_expr_with_expected(
                layout,
                call_ctx,
                spec_scope,
                ctx.local_tys,
                inferred,
                Some(&layout_spec_ty()),
            )?;
            ensure_raw_expr_ty(&layout, &layout_spec_ty(), "DeallocToken layout")?;
            Ok(TypedRawPattern::DeallocToken { base, layout })
        }
    }
}

fn typed_raw_expr(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<TypedExpr, String> {
    typed_body_expr(
        expr,
        call_ctx,
        DirectiveKind::RawAssert,
        spec_scope,
        local_tys,
        inferred,
    )
}

fn typed_raw_expr_with_expected(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
    expected: Option<&SpecTy>,
) -> Result<TypedExpr, String> {
    typed_body_expr_with_expected(
        expr,
        call_ctx,
        DirectiveKind::RawAssert,
        spec_scope,
        local_tys,
        inferred,
        false,
        expected,
    )
}

fn infer_value_pattern_types(
    pattern: &ValuePattern,
    expected: &SpecTy,
    call_ctx: SpecCallContext<'_>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    match pattern {
        ValuePattern::Bind(name) => {
            spec_scope
                .bind_let(name, DUMMY_SP, None, None)
                .map_err(|err| err.message)?;
            inferred.constrain(name, expected)
        }
        ValuePattern::Expr(expr) => {
            infer_body_expr_types_with_expected(
                expr,
                call_ctx,
                DirectiveKind::RawAssert,
                spec_scope,
                local_tys,
                inferred,
                false,
                Some(expected),
            )?;
            Ok(())
        }
        ValuePattern::SeqLit(items) => {
            let SpecTy::Seq(inner) = expected else {
                return Err(format!(
                    "sequence raw pattern requires `Seq<T>`, got {}",
                    display_spec_ty(expected)
                ));
            };
            for item in items {
                infer_value_pattern_types(item, inner, call_ctx, spec_scope, local_tys, inferred)?;
            }
            Ok(())
        }
        ValuePattern::StructLit { name, fields } => {
            let struct_fields = raw_pattern_struct_fields(expected, name, call_ctx.struct_defs)?;
            for field in fields {
                let field_ty = struct_fields
                    .iter()
                    .find(|item| item.name == field.name)
                    .ok_or_else(|| format!("unknown field `{}` in `{name}`", field.name))?;
                infer_value_pattern_types(
                    &field.value,
                    &field_ty.ty,
                    call_ctx,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            Ok(())
        }
        ValuePattern::Call {
            func,
            type_args,
            args,
        } => {
            let (enum_def, _) = lookup_enum_ctor(call_ctx.enum_defs, func)
                .ok_or_else(|| format!("unknown constructor `{func}`"))?;
            let mut bindings =
                explicit_enum_type_bindings(func, enum_def, type_args, call_ctx.enum_defs)?;
            let _ = seed_enum_type_param_bindings(enum_def, expected, &mut bindings)?;
            let (_, ctor) = enum_def
                .ctor(func.rsplit("::").next().unwrap_or(func))
                .ok_or_else(|| format!("unknown constructor `{func}`"))?;
            if ctor.fields.len() != args.len() {
                return Err(format!(
                    "constructor `{func}` expects {} arguments, found {}",
                    ctor.fields.len(),
                    args.len()
                ));
            }
            for (arg, field_ty) in args.iter().zip(&ctor.fields) {
                let expected_field_ty = try_instantiate_spec_ty(field_ty, &bindings)
                    .ok_or_else(|| format!("could not infer type arguments for `{func}`"))?;
                infer_value_pattern_types(
                    arg,
                    &expected_field_ty,
                    call_ctx,
                    spec_scope,
                    local_tys,
                    inferred,
                )?;
            }
            Ok(())
        }
    }
}

fn bind_value_pattern_vars(
    pattern: &ValuePattern,
    spec_scope: &mut SpecScope,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    match pattern {
        ValuePattern::Bind(name) => {
            spec_scope
                .bind_let(name, DUMMY_SP, None, None)
                .map_err(|err| err.message)?;
            inferred.ensure_var(name);
        }
        ValuePattern::Expr(_) => {}
        ValuePattern::SeqLit(items) | ValuePattern::Call { args: items, .. } => {
            for item in items {
                bind_value_pattern_vars(item, spec_scope, inferred)?;
            }
        }
        ValuePattern::StructLit { fields, .. } => {
            for field in fields {
                bind_value_pattern_vars(&field.value, spec_scope, inferred)?;
            }
        }
    }
    Ok(())
}

fn raw_pattern_struct_fields(
    expected: &SpecTy,
    name: &str,
    struct_defs: &HashMap<String, StructDef>,
) -> Result<Vec<StructFieldTy>, String> {
    match expected {
        SpecTy::Struct {
            name: struct_name, ..
        } if struct_name == name => struct_fields_for_ty(expected, struct_defs)?
            .ok_or_else(|| format!("unknown spec struct `{struct_name}`")),
        SpecTy::Struct {
            name: struct_name, ..
        } => Err(format!(
            "struct raw pattern `{name}` does not match `{struct_name}`"
        )),
        other => Err(format!(
            "struct raw pattern `{name}` requires a struct type, got {}",
            display_spec_ty(other)
        )),
    }
}

fn typed_value_pattern(
    pattern: &ValuePattern,
    expected: &SpecTy,
    call_ctx: SpecCallContext<'_>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<TypedValuePattern, String> {
    match pattern {
        ValuePattern::Bind(name) => {
            spec_scope
                .bind_let(name, DUMMY_SP, None, None)
                .map_err(|err| err.message)?;
            inferred.constrain(name, expected)?;
            Ok(TypedValuePattern::Bind {
                name: name.clone(),
                ty: expected.clone(),
            })
        }
        ValuePattern::Expr(expr) => Ok(TypedValuePattern::Expr(typed_body_expr_with_expected(
            expr,
            call_ctx,
            DirectiveKind::RawAssert,
            spec_scope,
            local_tys,
            inferred,
            false,
            Some(expected),
        )?)),
        ValuePattern::SeqLit(items) => {
            let SpecTy::Seq(inner) = expected else {
                return Err(format!(
                    "sequence raw pattern requires `Seq<T>`, got {}",
                    display_spec_ty(expected)
                ));
            };
            let mut typed_items = Vec::with_capacity(items.len());
            for item in items {
                typed_items.push(typed_value_pattern(
                    item, inner, call_ctx, spec_scope, local_tys, inferred,
                )?);
            }
            Ok(TypedValuePattern::SeqLit {
                ty: expected.clone(),
                items: typed_items,
            })
        }
        ValuePattern::StructLit { name, fields } => {
            let struct_fields = raw_pattern_struct_fields(expected, name, call_ctx.struct_defs)?;
            let mut typed_fields = Vec::with_capacity(fields.len());
            for field in fields {
                let field_ty = struct_fields
                    .iter()
                    .find(|item| item.name == field.name)
                    .ok_or_else(|| format!("unknown field `{}` in `{name}`", field.name))?;
                typed_fields.push(typed_value_pattern(
                    &field.value,
                    &field_ty.ty,
                    call_ctx,
                    spec_scope,
                    local_tys,
                    inferred,
                )?);
            }
            Ok(TypedValuePattern::StructLit {
                ty: expected.clone(),
                fields: typed_fields,
            })
        }
        ValuePattern::Call {
            func,
            type_args,
            args,
        } => {
            let (enum_def, ctor_index) = lookup_enum_ctor(call_ctx.enum_defs, func)
                .ok_or_else(|| format!("unknown constructor `{func}`"))?;
            let mut bindings =
                explicit_enum_type_bindings(func, enum_def, type_args, call_ctx.enum_defs)?;
            let _ = seed_enum_type_param_bindings(enum_def, expected, &mut bindings)?;
            let (_, ctor) = enum_def
                .ctor(func.rsplit("::").next().unwrap_or(func))
                .ok_or_else(|| format!("unknown constructor `{func}`"))?;
            if ctor.fields.len() != args.len() {
                return Err(format!(
                    "constructor `{func}` expects {} arguments, found {}",
                    ctor.fields.len(),
                    args.len()
                ));
            }
            let result_ty = instantiate_enum_result_ty(func, enum_def, &bindings)?;
            let _ = unify_spec_tys(&result_ty, expected)?;
            let mut typed_args = Vec::with_capacity(args.len());
            for (arg, field_ty) in args.iter().zip(&ctor.fields) {
                let expected_field_ty = try_instantiate_spec_ty(field_ty, &bindings)
                    .ok_or_else(|| format!("could not infer type arguments for `{func}`"))?;
                typed_args.push(typed_value_pattern(
                    arg,
                    &expected_field_ty,
                    call_ctx,
                    spec_scope,
                    local_tys,
                    inferred,
                )?);
            }
            Ok(TypedValuePattern::CtorCall {
                ty: result_ty,
                ctor_index,
                args: typed_args,
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn typed_standalone_fn_raw_assertions(
    assertions: &[RawAssertion],
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    rust_params: &HashMap<String, RustTypeExpr>,
    allow_result: bool,
    result_ty: &SpecTy,
    result_rust_ty: &RustTypeExpr,
    inferred: &mut SpecTypeInference,
) -> Result<Vec<RawAssertionContract>, String> {
    let mut out = Vec::with_capacity(assertions.len());
    for assertion in assertions {
        let pattern = typed_standalone_fn_raw_pattern(
            &assertion.pattern,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            rust_params,
            allow_result,
            result_ty,
            result_rust_ty,
            inferred,
        )?;
        let condition = typed_contract_expr_with_expected(
            &assertion.condition,
            pure_fns,
            enum_defs,
            struct_defs,
            &HashSet::new(),
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
            true,
            Some(&SpecTy::Bool),
        )?;
        out.push(RawAssertionContract {
            pattern,
            condition,
            resolution: ResolvedExprEnv::default(),
            assertion_span: "function contract raw clause".to_owned(),
        });
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn typed_standalone_fn_raw_pattern(
    pattern: &RawPattern,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    rust_params: &HashMap<String, RustTypeExpr>,
    allow_result: bool,
    result_ty: &SpecTy,
    result_rust_ty: &RustTypeExpr,
    inferred: &mut SpecTypeInference,
) -> Result<TypedRawPattern, String> {
    match pattern {
        RawPattern::Star(lhs, rhs) => Ok(TypedRawPattern::Star(
            Box::new(typed_standalone_fn_raw_pattern(
                lhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                rust_params,
                allow_result,
                result_ty,
                result_rust_ty,
                inferred,
            )?),
            Box::new(typed_standalone_fn_raw_pattern(
                rhs,
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                rust_params,
                allow_result,
                result_ty,
                result_rust_ty,
                inferred,
            )?),
        )),
        RawPattern::PointsToSugar { pointer, value } => {
            let pointer_rust_ty = if allow_result && pointer == "result" {
                result_rust_ty
            } else {
                rust_params
                    .get(pointer)
                    .ok_or_else(|| format!("unresolved pointer `{pointer}` in raw contract"))?
            };
            let pointee_text = raw_pointer_pointee_text(&pointer_rust_ty.text)?;
            let type_params = contract_type_param_scope(params, result_ty);
            let pointee_ty = rust_ty_key_to_spec_ty(pointee_text, &type_params)?;
            let addr = TypedExpr {
                ty: SpecTy::Usize,
                kind: TypedExprKind::Field {
                    base: Box::new(TypedExpr {
                        ty: ptr_spec_ty(),
                        kind: TypedExprKind::Var(pointer.clone()),
                    }),
                    name: "addr".to_owned(),
                    index: 0,
                },
            };
            let ty = TypedExpr {
                ty: SpecTy::RustTy,
                kind: TypedExprKind::RustType(RustTyKey::new(pointee_text.to_owned())),
            };
            let value = typed_contract_value_pattern(
                value,
                &option_spec_ty(pointee_ty),
                pure_fns,
                enum_defs,
                struct_defs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            Ok(TypedRawPattern::PointsTo { addr, ty, value })
        }
        RawPattern::Emp
        | RawPattern::PointsTo { .. }
        | RawPattern::Own { .. }
        | RawPattern::DeallocToken { .. } => typed_lemma_raw_pattern(
            pattern,
            pure_fns,
            enum_defs,
            struct_defs,
            spec_scope,
            params,
            allow_result,
            result_ty,
            inferred,
        ),
    }
}

fn raw_pointer_pointee_text(text: &str) -> Result<&str, String> {
    let text = text.trim();
    text.strip_prefix("*const ")
        .or_else(|| text.strip_prefix("*mut "))
        .map(str::trim)
        .ok_or_else(|| {
            format!(
                "`|-?->` raw pattern requires a raw pointer, found `{}`",
                text
            )
        })
}

fn ensure_raw_expr_ty(expr: &TypedExpr, expected: &SpecTy, label: &str) -> Result<(), String> {
    if &expr.ty == expected {
        Ok(())
    } else {
        Err(format!(
            "{label} must have type {}, got {}",
            display_spec_ty(expected),
            display_spec_ty(&expr.ty)
        ))
    }
}

fn ensure_option_raw_value(expr: &TypedExpr) -> Result<(), String> {
    match &expr.ty {
        SpecTy::Enum { name, args } if name == "Option" && args.len() == 1 => Ok(()),
        ty => Err(format!(
            "PointsTo value pattern must have type Option<T>, got {}",
            display_spec_ty(ty)
        )),
    }
}

fn value_pattern_contains_bind(pattern: &ValuePattern) -> bool {
    match pattern {
        ValuePattern::Bind(_) => true,
        ValuePattern::Expr(_) => false,
        ValuePattern::SeqLit(items) | ValuePattern::Call { args: items, .. } => {
            items.iter().any(value_pattern_contains_bind)
        }
        ValuePattern::StructLit { fields, .. } => fields
            .iter()
            .any(|field| value_pattern_contains_bind(&field.value)),
    }
}

fn contract_type_param_scope(
    params: &HashMap<String, SpecTy>,
    result_ty: &SpecTy,
) -> HashSet<String> {
    let mut type_params = HashSet::new();
    for ty in params.values() {
        collect_spec_ty_type_params(ty, &mut type_params);
    }
    collect_spec_ty_type_params(result_ty, &mut type_params);
    type_params
}

fn option_spec_ty_for_rust_ty_expr(
    expr: &TypedExpr,
    type_params: &HashSet<String>,
) -> Result<SpecTy, String> {
    let TypedExprKind::RustType(key) = &expr.kind else {
        return Err("PointsTo type must be a concrete Rust type expression".to_owned());
    };
    Ok(option_spec_ty(rust_ty_key_to_spec_ty(
        key.as_str(),
        type_params,
    )?))
}

fn rust_ty_key_to_spec_ty(key: &str, type_params: &HashSet<String>) -> Result<SpecTy, String> {
    match key {
        "bool" => Ok(SpecTy::Bool),
        "i8" => Ok(SpecTy::I8),
        "i16" => Ok(SpecTy::I16),
        "i32" => Ok(SpecTy::I32),
        "i64" => Ok(SpecTy::I64),
        "isize" => Ok(SpecTy::Isize),
        "u8" => Ok(SpecTy::U8),
        "u16" => Ok(SpecTy::U16),
        "u32" => Ok(SpecTy::U32),
        "u64" => Ok(SpecTy::U64),
        "usize" => Ok(SpecTy::Usize),
        raw if raw.starts_with("*const ") || raw.starts_with("*mut ") => Ok(ptr_spec_ty()),
        raw if raw.starts_with("&mut ") => Ok(SpecTy::Mut(Box::new(rust_ty_key_to_spec_ty(
            raw.trim_start_matches("&mut ").trim(),
            type_params,
        )?))),
        raw if raw.starts_with('&') => Ok(SpecTy::Ref(Box::new(rust_ty_key_to_spec_ty(
            raw.trim_start_matches('&').trim(),
            type_params,
        )?))),
        type_param if type_params.contains(type_param) => {
            Ok(SpecTy::TypeParam(type_param.to_owned()))
        }
        other => Err(format!(
            "unsupported PointsTo Rust type expression `{other}` in raw pattern"
        )),
    }
}

pub fn rust_ty_key_text_for_rust_ty(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Result<String, String> {
    Ok(match ty.kind() {
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
            format!("*{kind} {}", rust_ty_key_text_for_rust_ty(tcx, *pointee)?)
        }
        TyKind::Ref(_, inner, mutability) => {
            let inner = rust_ty_key_text_for_rust_ty(tcx, *inner)?;
            if mutability.is_mut() {
                format!("&mut {inner}")
            } else {
                format!("&{inner}")
            }
        }
        TyKind::Tuple(fields) => {
            let fields = fields
                .iter()
                .map(|field| rust_ty_key_text_for_rust_ty(tcx, field))
                .collect::<Result<Vec<_>, _>>()?;
            match fields.as_slice() {
                [] => "()".to_owned(),
                [field] => format!("({field},)"),
                _ => format!("({})", fields.join(", ")),
            }
        }
        TyKind::Adt(adt_def, args) => {
            let mut text = tcx.def_path_str(adt_def.did());
            let type_args = args
                .types()
                .map(|arg| rust_ty_key_text_for_rust_ty(tcx, arg))
                .collect::<Result<Vec<_>, _>>()?;
            if !type_args.is_empty() {
                text.push('<');
                text.push_str(&type_args.join(", "));
                text.push('>');
            }
            text
        }
        TyKind::Param(param) => param.name.to_string(),
        other => {
            return Err(format!("unsupported Rust type in raw pattern `{other:?}`"));
        }
    })
}

struct UnsafeBlockCollector {
    spans: Vec<Span>,
}

impl<'v> Visitor<'v> for UnsafeBlockCollector {
    fn visit_expr(&mut self, expr: &'v HirExpr<'v>) {
        if let ExprKind::Block(block, _) = expr.kind
            && matches!(
                block.rules,
                BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided)
            )
        {
            self.spans.push(block.span);
        }
        intravisit::walk_expr(self, expr);
    }
}

fn reject_directives_inside_unsafe_blocks(
    directives: &CollectedFunctionDirectives,
    unsafe_blocks: &[Span],
) -> Result<(), LoopPrepassError> {
    for directive in &directives.directives {
        if matches!(
            directive.kind,
            DirectiveKind::Req
                | DirectiveKind::Ens
                | DirectiveKind::Let
                | DirectiveKind::Assert
                | DirectiveKind::Assume
                | DirectiveKind::RawAssert
                | DirectiveKind::RawReq
                | DirectiveKind::RawEns
                | DirectiveKind::LemmaCall
        ) {
            continue;
        }
        if unsafe_blocks
            .iter()
            .any(|unsafe_span| span_contains(*unsafe_span, directive.span))
        {
            return Err(LoopPrepassError {
                span: directive.span,
                display_span: Some(directive.span_text.clone()),
                message: "spec directives inside unsafe blocks are unsupported".to_owned(),
            });
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn resolve_lemma_call_expr_env(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
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
        let arg_env = resolve_expr_env_in_scope(
            arg,
            pure_fns,
            enum_defs,
            type_param_scope,
            binding_info,
            hir_locals,
            span,
            anchor_span,
            DirectiveKind::LemmaCall,
            spec_scope,
        )?;
        resolved.locals.extend(arg_env.locals);
    }
    Ok(resolved)
}

fn infer_lemma_call(
    expr: &Expr,
    lemmas: &HashMap<String, LemmaDef>,
    call_ctx: SpecCallContext<'_>,
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
    let mut bindings = seed_lemma_type_bindings(
        lemma_name,
        &lemma.type_params,
        type_args,
        call_ctx.enum_defs,
        call_ctx.type_param_scope,
    )?;
    let mut arg_tys = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&lemma.params) {
        let expected = try_instantiate_spec_ty(&param.ty, &bindings);
        let arg_ty = infer_body_expr_types_with_expected(
            arg,
            call_ctx,
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

fn typed_lemma_call(
    expr: &Expr,
    span_text: &str,
    lemmas: &HashMap<String, LemmaDef>,
    call_ctx: SpecCallContext<'_>,
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
    let mut bindings = seed_lemma_type_bindings(
        lemma_name,
        &lemma.type_params,
        type_args,
        call_ctx.enum_defs,
        call_ctx.type_param_scope,
    )?;
    let mut typed_args = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(&lemma.params) {
        let expected = try_instantiate_spec_ty(&param.ty, &bindings);
        let typed = typed_body_expr_with_expected(
            arg,
            call_ctx,
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
        TypedExprKind::SeqLit(items) | TypedExprKind::StructLit { fields: items } => items
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
        | TypedExprKind::VariantSelector { base, .. }
        | TypedExprKind::Cast { arg: base }
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
        | TypedExprKind::RustType(_) => false,
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
        TypedExprKind::SeqLit(items) | TypedExprKind::StructLit { fields: items } => {
            for item in items {
                validate_recursive_pure_expr(item, ctx, allowed_recursive_vars)?;
            }
            Ok(())
        }
        TypedExprKind::Field { base, .. }
        | TypedExprKind::TupleField { base, .. }
        | TypedExprKind::VariantSelector { base, .. }
        | TypedExprKind::Cast { arg: base }
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
        | TypedExprKind::RustType(_) => Ok(()),
    }
}

fn validate_recursive_pure_fn(def: &TypedPureFnDef) -> Result<(), String> {
    let Some(body) = &def.body else {
        return Ok(());
    };
    if !typed_expr_calls_pure_fn(body, &def.name) {
        return Ok(());
    }
    let TypedExprKind::Match {
        scrutinee,
        arms,
        default,
    } = &body.kind
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
    if !matches!(recursive_param.ty, SpecTy::Enum { .. }) {
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
    struct_defs: &HashMap<String, StructDef>,
    span: Span,
) -> Result<Vec<TypedPureFnDef>, LoopPrepassError> {
    let mut available_pure_fns = HashMap::new();
    let mut typed = Vec::with_capacity(declaration_order.len());
    for name in declaration_order {
        let def = pure_fns
            .get(name)
            .expect("pure function declaration order must stay in sync");
        available_pure_fns.insert(def.name.clone(), def.clone());
        let type_param_scope: HashSet<_> = def.type_params.iter().cloned().collect();
        for param in &def.params {
            validate_named_spec_ty(&param.ty, enum_defs, &type_param_scope).map_err(|message| {
                LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "pure function `{}` parameter `{}`: {message}",
                        def.name, param.name
                    ),
                }
            })?;
        }
        validate_named_spec_ty(&def.result_ty, enum_defs, &type_param_scope).map_err(
            |message| LoopPrepassError {
                span,
                display_span: None,
                message: format!("pure function `{}` result: {message}", def.name),
            },
        )?;
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
        let Some(raw_body) = &def.body else {
            typed.push(TypedPureFnDef {
                name: def.name.clone(),
                params,
                result_ty: def.result_ty.clone(),
                body: None,
            });
            continue;
        };
        let mut inferred = SpecTypeInference::default();
        let mut infer_scope = SpecScope::default();
        infer_contract_expr_types_in_scope(
            raw_body,
            &available_pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
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
        let body = typed_contract_expr_in_scope(
            raw_body,
            &available_pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
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
            result_ty: def.result_ty.clone(),
            body: Some(body),
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
    struct_defs: &HashMap<String, StructDef>,
    type_param_scope: &HashSet<String>,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            crate::spec::GhostStmt::Assert(expr) | crate::spec::GhostStmt::Assume(expr) => {
                infer_contract_expr_types_in_scope(
                    expr,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    local_tys,
                    false,
                    result_ty,
                    inferred,
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
                        struct_defs,
                        type_param_scope,
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
                let scrutinee_ty = infer_contract_expr_types_in_scope(
                    scrutinee,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    local_tys,
                    false,
                    result_ty,
                    inferred,
                )?;
                let InferredExprTy::Known(SpecTy::Enum {
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
                        struct_defs,
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
                        struct_defs,
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
    struct_defs: &HashMap<String, StructDef>,
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
                let typed_expr = typed_contract_expr_in_scope(
                    expr,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    local_tys,
                    false,
                    result_ty,
                    inferred,
                )?;
                typed.push(TypedGhostStmt::Assert(normalize_assert_like_predicate(
                    typed_expr,
                    "ghost assert",
                )?))
            }
            crate::spec::GhostStmt::Assume(expr) => {
                let typed_expr = typed_contract_expr_in_scope(
                    expr,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    local_tys,
                    false,
                    result_ty,
                    inferred,
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
                        struct_defs,
                        type_param_scope,
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
                let scrutinee = typed_contract_expr_in_scope(
                    scrutinee,
                    pure_fns,
                    enum_defs,
                    struct_defs,
                    type_param_scope,
                    spec_scope,
                    local_tys,
                    false,
                    result_ty,
                    inferred,
                )?;
                let SpecTy::Enum {
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
                        struct_defs,
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
                        struct_defs,
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
        TypedExprKind::RustVar(_) | TypedExprKind::RustType(_) => None,
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
                    TypedExprKind::RustVar(_) | TypedExprKind::RustType(_) => None,
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
    if !matches!(def.params[induction_param_index].ty, SpecTy::Enum { .. }) {
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
    struct_defs: &HashMap<String, StructDef>,
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
        if !lemma.is_unsafe && (!lemma.raw_reqs.is_empty() || !lemma.raw_ens.is_empty()) {
            return Err(LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "lemma `{}` raw contracts are only supported on unsafe lemmas",
                    lemma.name
                ),
            });
        }
        let result_ty = SpecTy::Bool;
        let mut inferred = SpecTypeInference::default();
        let mut infer_scope = SpecScope::default();
        infer_contract_expr_types_in_scope(
            &lemma.req,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
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
        for resource_req in &lemma.raw_reqs {
            infer_contract_raw_assertion(
                resource_req,
                pure_fns,
                enum_defs,
                struct_defs,
                &mut body_infer_scope,
                &param_tys,
                false,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!("lemma `{}` raw req: {message}", lemma.name),
            })?;
        }
        infer_lemma_stmts(
            &lemma.body,
            &visible_lemmas,
            lemmas,
            pure_fns,
            enum_defs,
            struct_defs,
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
        infer_contract_expr_types_in_scope(
            &lemma.ens,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
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
        let req = typed_contract_expr_in_scope(
            &lemma.req,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
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
        let raw_reqs = typed_lemma_raw_assertions(
            &lemma.raw_reqs,
            pure_fns,
            enum_defs,
            struct_defs,
            &mut type_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` raw req: {message}", lemma.name),
        })?;
        let body = typed_lemma_stmts(
            &lemma.body,
            &visible_lemmas,
            lemmas,
            pure_fns,
            enum_defs,
            struct_defs,
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
        let ens = typed_contract_expr_in_scope(
            &lemma.ens,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
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
        for raw_ens in &lemma.raw_ens {
            infer_contract_raw_assertion(
                raw_ens,
                pure_fns,
                enum_defs,
                struct_defs,
                &mut body_infer_scope,
                &param_tys,
                false,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!("lemma `{}` raw ens: {message}", lemma.name),
            })?;
        }
        let raw_ens = typed_lemma_raw_assertions(
            &lemma.raw_ens,
            pure_fns,
            enum_defs,
            struct_defs,
            &mut type_scope,
            &param_tys,
            false,
            &result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!("lemma `{}` raw ens: {message}", lemma.name),
        })?;
        let typed_def = TypedLemmaDef {
            name: lemma.name.clone(),
            is_unsafe: lemma.is_unsafe,
            params,
            req,
            raw_reqs,
            ens,
            raw_ens,
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

fn type_standalone_fn_contracts(
    standalone_fn_contracts: &HashMap<String, StandaloneFnContractDef>,
    declaration_order: &[String],
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    struct_defs: &HashMap<String, StructDef>,
    span: Span,
) -> Result<HashMap<String, FunctionContract>, LoopPrepassError> {
    let mut typed = HashMap::new();
    for path in declaration_order {
        let def = standalone_fn_contracts
            .get(path)
            .expect("function contract declaration order must stay in sync");
        let type_param_scope: HashSet<_> = def.type_params.iter().cloned().collect();
        for param in &def.params {
            validate_named_spec_ty(&param.ty, enum_defs, &type_param_scope).map_err(|message| {
                LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "function contract declaration `{}` parameter `{}`: {message}",
                        def.path, param.name
                    ),
                }
            })?;
        }
        validate_named_spec_ty(&def.result_ty, enum_defs, &type_param_scope).map_err(
            |message| LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "function contract declaration `{}` result: {message}",
                    def.path
                ),
            },
        )?;
        if !def.is_unsafe && (!def.raw_reqs.is_empty() || !def.raw_ens.is_empty()) {
            return Err(LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "function contract declaration `{}` raw contracts are only supported on unsafe functions",
                    def.path
                ),
            });
        }

        let param_tys: HashMap<_, _> = def
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        let rust_param_tys: HashMap<_, _> = def
            .params
            .iter()
            .map(|param| (param.name.clone(), param.rust_ty.clone()))
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
        infer_contract_expr_types_in_scope(
            &def.req,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
            &mut infer_scope,
            &param_tys,
            false,
            &def.result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!(
                "function contract declaration `{}` req: {message}",
                def.path
            ),
        })?;
        let mut ens_infer_scope = infer_scope.clone();
        for resource_req in &def.raw_reqs {
            infer_contract_raw_assertion(
                resource_req,
                pure_fns,
                enum_defs,
                struct_defs,
                &mut ens_infer_scope,
                &param_tys,
                false,
                &def.result_ty,
                &mut inferred,
            )
            .map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "function contract declaration `{}` raw req: {message}",
                    def.path
                ),
            })?;
        }
        infer_contract_expr_types_in_scope(
            &def.ens,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
            &mut ens_infer_scope,
            &param_tys,
            true,
            &def.result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!(
                "function contract declaration `{}` ens: {message}",
                def.path
            ),
        })?;
        for raw_ens in &def.raw_ens {
            infer_contract_raw_assertion(
                raw_ens,
                pure_fns,
                enum_defs,
                struct_defs,
                &mut ens_infer_scope,
                &param_tys,
                true,
                &def.result_ty,
                &mut inferred,
            )
            .map_err(|message| LoopPrepassError {
                span,
                display_span: None,
                message: format!(
                    "function contract declaration `{}` raw ens: {message}",
                    def.path
                ),
            })?;
        }

        let mut type_scope = SpecScope::default();
        let req = typed_contract_expr_in_scope(
            &def.req,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
            &mut type_scope,
            &param_tys,
            false,
            &def.result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!(
                "function contract declaration `{}` req: {message}",
                def.path
            ),
        })
        .and_then(|expr| {
            normalize_assert_like_predicate(expr, "function contract req").map_err(|message| {
                LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "function contract declaration `{}` req: {message}",
                        def.path
                    ),
                }
            })
        })?;
        let raw_reqs = typed_standalone_fn_raw_assertions(
            &def.raw_reqs,
            pure_fns,
            enum_defs,
            struct_defs,
            &mut type_scope,
            &param_tys,
            &rust_param_tys,
            false,
            &def.result_ty,
            &def.result_rust_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!(
                "function contract declaration `{}` raw req: {message}",
                def.path
            ),
        })?;
        let ens = typed_contract_expr_in_scope(
            &def.ens,
            pure_fns,
            enum_defs,
            struct_defs,
            &type_param_scope,
            &mut type_scope,
            &param_tys,
            true,
            &def.result_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!(
                "function contract declaration `{}` ens: {message}",
                def.path
            ),
        })
        .and_then(|expr| {
            ensure_bind_free_predicate(expr, "function contract ens").map_err(|message| {
                LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!(
                        "function contract declaration `{}` ens: {message}",
                        def.path
                    ),
                }
            })
        })?;
        let raw_ens = typed_standalone_fn_raw_assertions(
            &def.raw_ens,
            pure_fns,
            enum_defs,
            struct_defs,
            &mut type_scope,
            &param_tys,
            &rust_param_tys,
            true,
            &def.result_ty,
            &def.result_rust_ty,
            &mut inferred,
        )
        .map_err(|message| LoopPrepassError {
            span,
            display_span: None,
            message: format!(
                "function contract declaration `{}` raw ens: {message}",
                def.path
            ),
        })?;
        typed.insert(
            def.path.clone(),
            FunctionContract {
                params,
                req,
                req_span: format!("function contract declaration `{}` req", def.path),
                raw_reqs,
                ens,
                ens_span: format!("function contract declaration `{}` ens", def.path),
                raw_ens,
                result: def.result_ty.clone(),
            },
        );
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
    origin: &GhostSourceOrigin,
    sink: &mut GhostItemSink<'_>,
) -> Result<(), LoopPrepassError> {
    for parsed in collect_ghost_blocks(source).map_err(|err| LoopPrepassError {
        span: error_span,
        display_span: None,
        message: origin.parse_error_message(&err),
    })? {
        sink.enums.extend(parsed.enums);
        sink.structs.extend(parsed.structs);
        sink.pure_fns.extend(parsed.pure_fns);
        sink.lemmas.extend(parsed.lemmas);
        sink.standalone_fn_contracts
            .extend(parsed.standalone_fn_contracts);
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
    type_param_scope: &HashSet<String>,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), LoopPrepassError> {
    validate_contract_expr_core(
        expr,
        SpecCallContext {
            pure_fns,
            enum_defs,
            struct_defs: prelude_struct_defs(),
            type_param_scope,
        },
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

fn validate_function_contract_raw_prepass(
    directive: &FunctionDirective,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), LoopPrepassError> {
    let assertion = directive.raw_assertion().expect("raw contract payload");
    validate_function_contract_raw_pattern_prepass(
        &assertion.pattern,
        directive,
        pure_fns,
        enum_defs,
        type_param_scope,
        params,
        allow_result,
        spec_scope,
    )?;
    validate_function_contract_expr_prepass(
        directive.span,
        &directive.span_text,
        &assertion.condition,
        pure_fns,
        enum_defs,
        type_param_scope,
        params,
        allow_result,
        spec_scope,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_function_contract_raw_pattern_prepass(
    pattern: &RawPattern,
    directive: &FunctionDirective,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), LoopPrepassError> {
    match pattern {
        RawPattern::Emp => Ok(()),
        RawPattern::Star(lhs, rhs) => {
            validate_function_contract_raw_pattern_prepass(
                lhs,
                directive,
                pure_fns,
                enum_defs,
                type_param_scope,
                params,
                allow_result,
                spec_scope,
            )?;
            validate_function_contract_raw_pattern_prepass(
                rhs,
                directive,
                pure_fns,
                enum_defs,
                type_param_scope,
                params,
                allow_result,
                spec_scope,
            )
        }
        RawPattern::PointsTo { addr, ty, value } => {
            for expr in [addr, ty] {
                validate_function_contract_expr_prepass(
                    directive.span,
                    &directive.span_text,
                    expr,
                    pure_fns,
                    enum_defs,
                    type_param_scope,
                    params,
                    allow_result,
                    spec_scope,
                )?;
            }
            validate_function_contract_value_pattern_prepass(
                value,
                directive,
                pure_fns,
                enum_defs,
                type_param_scope,
                params,
                allow_result,
                spec_scope,
            )
        }
        RawPattern::PointsToSugar { pointer, value } => {
            if !(params.iter().any(|param| param == pointer)
                || (allow_result && pointer == "result"))
            {
                return Err(LoopPrepassError {
                    span: directive.span,
                    display_span: Some(directive.span_text.clone()),
                    message: format!("unresolved pointer `{pointer}` in raw contract"),
                });
            }
            validate_function_contract_value_pattern_prepass(
                value,
                directive,
                pure_fns,
                enum_defs,
                type_param_scope,
                params,
                allow_result,
                spec_scope,
            )
        }
        RawPattern::Own { value, .. } => validate_function_contract_value_pattern_prepass(
            value,
            directive,
            pure_fns,
            enum_defs,
            type_param_scope,
            params,
            allow_result,
            spec_scope,
        ),
        RawPattern::DeallocToken { base, layout } => {
            for expr in [base, layout] {
                validate_function_contract_expr_prepass(
                    directive.span,
                    &directive.span_text,
                    expr,
                    pure_fns,
                    enum_defs,
                    type_param_scope,
                    params,
                    allow_result,
                    spec_scope,
                )?;
            }
            Ok(())
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_function_contract_value_pattern_prepass(
    pattern: &ValuePattern,
    directive: &FunctionDirective,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), LoopPrepassError> {
    match pattern {
        ValuePattern::Bind(name) => {
            spec_scope.bind_let(
                name,
                directive.span,
                Some(directive.span_text.clone()),
                None,
            )?;
            Ok(())
        }
        ValuePattern::Expr(expr) => validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            expr,
            pure_fns,
            enum_defs,
            type_param_scope,
            params,
            allow_result,
            spec_scope,
        ),
        ValuePattern::SeqLit(items) | ValuePattern::Call { args: items, .. } => {
            for item in items {
                validate_function_contract_value_pattern_prepass(
                    item,
                    directive,
                    pure_fns,
                    enum_defs,
                    type_param_scope,
                    params,
                    allow_result,
                    spec_scope,
                )?;
            }
            Ok(())
        }
        ValuePattern::StructLit { fields, .. } => {
            for field in fields {
                validate_function_contract_value_pattern_prepass(
                    &field.value,
                    directive,
                    pure_fns,
                    enum_defs,
                    type_param_scope,
                    params,
                    allow_result,
                    spec_scope,
                )?;
            }
            Ok(())
        }
    }
}

fn validate_contract_expr_core(
    expr: &Expr,
    call_ctx: SpecCallContext<'_>,
    spec_scope: &mut SpecScope,
    params: &[String],
    allow_result: bool,
    allow_bare_names: bool,
) -> Result<(), String> {
    match expr {
        Expr::Bool(_) | Expr::Int(_) | Expr::RustType(_) => Ok(()),
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
                    call_ctx,
                    spec_scope,
                    params,
                    allow_result,
                    allow_bare_names,
                )?;
            }
            Ok(())
        }
        Expr::StructLit { fields, .. } => {
            for field in fields {
                validate_contract_expr_core(
                    &field.value,
                    call_ctx,
                    spec_scope,
                    params,
                    allow_result,
                    allow_bare_names,
                )?;
            }
            Ok(())
        }
        Expr::Match { .. } => Err(unsupported_match_expr_message()),
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(call_ctx.enum_defs, func) {
                let ctor = &enum_def.ctors[ctor_index];
                if ctor.fields.len() != args.len() {
                    return Err(format!(
                        "constructor `{func}` expects {} arguments, found {}",
                        ctor.fields.len(),
                        args.len()
                    ));
                }
                validate_ctor_type_args(func, enum_def, type_args, call_ctx)?;
            } else {
                validate_pure_call_signature(func, type_args, args.len(), call_ctx)?;
            }
            for arg in args {
                validate_contract_expr_core(
                    arg,
                    call_ctx,
                    spec_scope,
                    params,
                    allow_result,
                    allow_bare_names,
                )?;
            }
            Ok(())
        }
        Expr::Field { base, .. }
        | Expr::TupleField { base, .. }
        | Expr::Deref { base }
        | Expr::Cast { arg: base, .. }
        | Expr::VariantSelector { base, .. } => validate_contract_expr_core(
            base,
            call_ctx,
            spec_scope,
            params,
            allow_result,
            allow_bare_names,
        ),
        Expr::Index { base, index } => {
            validate_contract_expr_core(
                base,
                call_ctx,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )?;
            validate_contract_expr_core(
                index,
                call_ctx,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )
        }
        Expr::Unary { arg, .. } => validate_contract_expr_core(
            arg,
            call_ctx,
            spec_scope,
            params,
            allow_result,
            allow_bare_names,
        ),
        Expr::Binary { lhs, rhs, .. } => {
            validate_contract_expr_core(
                lhs,
                call_ctx,
                spec_scope,
                params,
                allow_result,
                allow_bare_names,
            )?;
            validate_contract_expr_core(
                rhs,
                call_ctx,
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
    let type_param_scope = HashSet::new();
    resolve_expr_env_in_scope(
        expr,
        pure_fns,
        enum_defs,
        &type_param_scope,
        binding_info,
        hir_locals,
        span,
        anchor_span,
        kind,
        spec_scope,
    )
}

#[allow(clippy::too_many_arguments)]
fn resolve_expr_env_in_scope(
    expr: &Expr,
    pure_fns: &HashMap<String, PureFnDef>,
    enum_defs: &HashMap<String, EnumDef>,
    type_param_scope: &HashSet<String>,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
) -> Result<ResolvedExprEnv, LoopPrepassError> {
    let mut resolved = ResolvedExprEnv::default();
    let mut ctx = ExprResolutionContext {
        call_ctx: SpecCallContext {
            pure_fns,
            enum_defs,
            struct_defs: prelude_struct_defs(),
            type_param_scope,
        },
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
        Expr::Bool(_) | Expr::Int(_) | Expr::RustType(_) => Ok(()),
        Expr::Var(name) => {
            if ctx.spec_scope.visible.contains(name) {
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
        Expr::StructLit { fields, .. } => {
            for field in fields {
                resolve_expr_env_into(&field.value, ctx, resolved)?;
            }
            Ok(())
        }
        Expr::Match { .. } => Err(LoopPrepassError {
            span: ctx.span,
            display_span: None,
            message: unsupported_match_expr_message(),
        }),
        Expr::Call {
            func,
            type_args,
            args,
        } => {
            if let Some((enum_def, ctor_index)) = lookup_enum_ctor(ctx.call_ctx.enum_defs, func) {
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
                validate_ctor_type_args(func, enum_def, type_args, ctx.call_ctx).map_err(
                    |message| LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message,
                    },
                )?;
            } else {
                validate_pure_call_signature(func, type_args, args.len(), ctx.call_ctx).map_err(
                    |message| LoopPrepassError {
                        span: ctx.span,
                        display_span: None,
                        message,
                    },
                )?;
            }
            for arg in args {
                resolve_expr_env_into(arg, ctx, resolved)?;
            }
            Ok(())
        }
        Expr::Field { base, .. }
        | Expr::TupleField { base, .. }
        | Expr::Deref { base }
        | Expr::Cast { arg: base, .. }
        | Expr::VariantSelector { base, .. } => resolve_expr_env_into(base, ctx, resolved),
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

    fn true_expr() -> Expr {
        Expr::Bool(true)
    }

    #[test]
    fn preserves_user_pure_call_for_engine_encoding() {
        let pure_fns = HashMap::from([(
            "id".to_owned(),
            PureFnDef {
                name: "id".to_owned(),
                type_params: vec![],
                params: vec![PureFnParam {
                    name: "x".to_owned(),
                    ty: SpecTy::I32,
                }],
                result_ty: SpecTy::I32,
                body: Some(Expr::Var("x".to_owned())),
            },
        )]);

        let typed = type_pure_call(
            "id",
            &[],
            &[Expr::Var("arg".to_owned())],
            SpecCallContext {
                pure_fns: &pure_fns,
                enum_defs: &HashMap::new(),
                struct_defs: &HashMap::new(),
                type_param_scope: &HashSet::new(),
            },
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
    fn types_generic_pure_call_with_inferred_type_args() {
        let pure_fns = HashMap::from([(
            "seq_rev".to_owned(),
            PureFnDef {
                name: "seq_rev".to_owned(),
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                result_ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                body: Some(Expr::Var("xs".to_owned())),
            },
        )]);

        let typed = type_pure_call(
            "seq_rev",
            &[],
            &[Expr::Var("arg".to_owned())],
            SpecCallContext {
                pure_fns: &pure_fns,
                enum_defs: &HashMap::new(),
                struct_defs: &HashMap::new(),
                type_param_scope: &HashSet::new(),
            },
            &mut |expr, expected| {
                assert_eq!(expr, &Expr::Var("arg".to_owned()));
                assert_eq!(expected, None);
                Ok(TypedExpr {
                    ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                    kind: TypedExprKind::Var("arg".to_owned()),
                })
            },
        )
        .expect("typed generic pure call");

        assert_eq!(typed.ty, SpecTy::Seq(Box::new(SpecTy::I32)));
        assert!(matches!(
            typed.kind,
            TypedExprKind::PureCall { func, .. } if func == "seq_rev"
        ));
    }

    #[test]
    fn types_generic_pure_call_with_explicit_type_args() {
        let pure_fns = HashMap::from([(
            "seq_rev".to_owned(),
            PureFnDef {
                name: "seq_rev".to_owned(),
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                result_ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                body: Some(Expr::Var("xs".to_owned())),
            },
        )]);

        let typed = type_pure_call(
            "seq_rev",
            &[SpecTy::I32],
            &[Expr::Var("arg".to_owned())],
            SpecCallContext {
                pure_fns: &pure_fns,
                enum_defs: &HashMap::new(),
                struct_defs: &HashMap::new(),
                type_param_scope: &HashSet::new(),
            },
            &mut |expr, expected| {
                assert_eq!(expr, &Expr::Var("arg".to_owned()));
                assert_eq!(expected, Some(&SpecTy::Seq(Box::new(SpecTy::I32))));
                Ok(TypedExpr {
                    ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                    kind: TypedExprKind::Var("arg".to_owned()),
                })
            },
        )
        .expect("typed generic pure call with explicit type args");

        assert_eq!(typed.ty, SpecTy::Seq(Box::new(SpecTy::I32)));
    }

    #[test]
    fn types_generic_pure_call_with_sequence_literal_argument() {
        let pure_fns = HashMap::from([(
            "seq_rev".to_owned(),
            PureFnDef {
                name: "seq_rev".to_owned(),
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                result_ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                body: Some(Expr::Var("xs".to_owned())),
            },
        )]);

        let typed = typed_contract_expr_in_scope(
            &Expr::Call {
                func: "seq_rev".to_owned(),
                type_args: vec![],
                args: vec![Expr::SeqLit(vec![Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(crate::spec::IntSuffix::I32),
                })])],
            },
            &pure_fns,
            &HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
            &mut SpecScope::default(),
            &HashMap::new(),
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
        )
        .expect("typed generic pure call from literal");

        assert_eq!(typed.ty, SpecTy::Seq(Box::new(SpecTy::I32)));
    }

    #[test]
    fn infers_generic_pure_call_in_body_context() {
        let pure_fns = HashMap::from([(
            "seq_rev".to_owned(),
            PureFnDef {
                name: "seq_rev".to_owned(),
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                result_ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                body: Some(Expr::Var("xs".to_owned())),
            },
        )]);
        let enum_defs = HashMap::new();
        let struct_defs = HashMap::new();
        let type_param_scope = HashSet::new();
        let call_ctx = SpecCallContext::new(&pure_fns, &enum_defs, &struct_defs, &type_param_scope);

        let inferred = infer_body_expr_types_with_expected(
            &Expr::Call {
                func: "seq_rev".to_owned(),
                type_args: vec![],
                args: vec![Expr::SeqLit(vec![Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(crate::spec::IntSuffix::I32),
                })])],
            },
            call_ctx,
            DirectiveKind::Assert,
            &mut SpecScope::default(),
            &HashMap::new(),
            &mut SpecTypeInference::default(),
            false,
            None,
        )
        .expect("inferred generic pure call in body");

        assert_eq!(
            known_spec_ty(&inferred),
            Some(SpecTy::Seq(Box::new(SpecTy::I32)))
        );
    }

    #[test]
    fn types_generic_pure_call_equality_in_body_context() {
        let pure_fns = HashMap::from([(
            "seq_rev".to_owned(),
            PureFnDef {
                name: "seq_rev".to_owned(),
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                result_ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                body: Some(Expr::Var("xs".to_owned())),
            },
        )]);
        let enum_defs = HashMap::new();
        let struct_defs = HashMap::new();
        let type_param_scope = HashSet::new();
        let call_ctx = SpecCallContext::new(&pure_fns, &enum_defs, &struct_defs, &type_param_scope);

        let typed = typed_body_expr(
            &Expr::Binary {
                op: crate::spec::BinaryOp::Eq,
                lhs: Box::new(Expr::Call {
                    func: "seq_rev".to_owned(),
                    type_args: vec![],
                    args: vec![Expr::SeqLit(vec![Expr::Int(IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(crate::spec::IntSuffix::I32),
                    })])],
                }),
                rhs: Box::new(Expr::SeqLit(vec![Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(crate::spec::IntSuffix::I32),
                })])),
            },
            call_ctx,
            DirectiveKind::Assert,
            &mut SpecScope::default(),
            &HashMap::new(),
            &mut SpecTypeInference::default(),
        )
        .expect("typed body equality over generic pure call");

        assert_eq!(typed.ty, SpecTy::Bool);
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
                        field_names: vec![],
                    },
                    EnumCtorDef {
                        name: "Cons".to_owned(),
                        fields: vec![
                            SpecTy::TypeParam("T".to_owned()),
                            SpecTy::Enum {
                                name: "List".to_owned(),
                                args: vec![SpecTy::TypeParam("T".to_owned())],
                            },
                        ],
                        field_names: vec![Some("head".to_owned()), Some("tail".to_owned())],
                    },
                ],
                invariant: None,
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

        let typed = typed_contract_expr_in_scope(
            &expr,
            &HashMap::new(),
            &enum_defs,
            &HashMap::new(),
            &HashSet::new(),
            &mut SpecScope::default(),
            &HashMap::new(),
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
        )
        .expect("typed constructor call");

        assert_eq!(
            typed.ty,
            SpecTy::Enum {
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
    fn types_struct_variant_selector_with_inferred_type_args() {
        let enum_defs = HashMap::from([(
            "List".to_owned(),
            EnumDef {
                name: "List".to_owned(),
                type_params: vec!["T".to_owned()],
                ctors: vec![
                    EnumCtorDef {
                        name: "Nil".to_owned(),
                        fields: vec![],
                        field_names: vec![],
                    },
                    EnumCtorDef {
                        name: "Cons".to_owned(),
                        fields: vec![
                            SpecTy::TypeParam("T".to_owned()),
                            SpecTy::Enum {
                                name: "List".to_owned(),
                                args: vec![SpecTy::TypeParam("T".to_owned())],
                            },
                        ],
                        field_names: vec![Some("head".to_owned()), Some("tail".to_owned())],
                    },
                ],
                invariant: None,
            },
        )]);
        let struct_defs = HashMap::from([(
            "List::Cons".to_owned(),
            StructDef {
                name: "List::Cons".to_owned(),
                type_params: vec!["T".to_owned()],
                fields: vec![
                    StructFieldTy {
                        name: "head".to_owned(),
                        ty: SpecTy::TypeParam("T".to_owned()),
                    },
                    StructFieldTy {
                        name: "tail".to_owned(),
                        ty: SpecTy::Enum {
                            name: "List".to_owned(),
                            args: vec![SpecTy::TypeParam("T".to_owned())],
                        },
                    },
                ],
                invariant: None,
            },
        )]);
        let params = HashMap::from([(
            "xs".to_owned(),
            SpecTy::Enum {
                name: "List".to_owned(),
                args: vec![SpecTy::I32],
            },
        )]);
        let expr = Expr::Field {
            base: Box::new(Expr::VariantSelector {
                base: Box::new(Expr::Var("xs".to_owned())),
                enum_name: "List".to_owned(),
                ctor_name: "Cons".to_owned(),
                type_args: vec![],
            }),
            name: "head".to_owned(),
        };

        let typed = typed_contract_expr_in_scope(
            &expr,
            &HashMap::new(),
            &enum_defs,
            &struct_defs,
            &HashSet::new(),
            &mut SpecScope::default(),
            &params,
            false,
            &SpecTy::Bool,
            &mut SpecTypeInference::default(),
        )
        .expect("typed selector field");

        assert_eq!(typed.ty, SpecTy::I32);
    }

    #[test]
    fn types_generic_lemma_call_with_inferred_type_args() {
        let lemmas = HashMap::from([(
            "seq_concat_empty_right".to_owned(),
            LemmaDef {
                name: "seq_concat_empty_right".to_owned(),
                is_unsafe: false,
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                req: true_expr(),
                raw_reqs: vec![],
                ens: true_expr(),
                raw_ens: vec![],
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
            SpecCallContext {
                pure_fns: &HashMap::new(),
                enum_defs: &HashMap::new(),
                struct_defs: &HashMap::new(),
                type_param_scope: &HashSet::new(),
            },
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
            structs: HashMap::new(),
            struct_invariants: HashMap::new(),
            enum_invariants: HashMap::new(),
            typed_pure_fns: vec![TypedPureFnDef {
                name: "id".to_owned(),
                params: Vec::new(),
                result_ty: SpecTy::I32,
                body: Some(TypedExpr {
                    ty: SpecTy::I32,
                    kind: TypedExprKind::Int(IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(crate::spec::IntSuffix::I32),
                    }),
                }),
            }],
            typed_lemmas: Vec::new(),
            standalone_fn_contracts: HashMap::new(),
        };

        assert_eq!(ghosts.typed_pure_fns.len(), 1);
        assert!(ghosts.typed_lemmas.is_empty());
    }
}
