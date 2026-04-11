use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::ops::ControlFlow;

use crate::directive::{
    CollectedFunctionDirectives, DirectiveAttach, DirectiveError, DirectiveKind, FunctionDirective,
    collect_function_directives,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{Expr, SpecTy, TypedExpr, TypedExprKind};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{HirId, ItemKind, Pat, PatKind};
use rustc_middle::mir::{BasicBlock, Body, Local, PlaceElem, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};

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
pub struct AssertionContracts {
    pub by_control_point: HashMap<(BasicBlock, usize), AssertionContract>,
}

#[derive(Debug, Clone)]
pub struct AssumptionContract {
    pub assumption: TypedExpr,
    pub resolution: ResolvedExprEnv,
}

#[derive(Debug, Clone)]
pub struct AssumptionContracts {
    pub by_control_point: HashMap<(BasicBlock, usize), AssumptionContract>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutoInvariantKind {
    Trivial,
    I32Range,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractValueOrigin {
    Direct,
    Current,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractValueSpec {
    pub ty: SpecTy,
    pub invariant: AutoInvariantKind,
    pub origin: ContractValueOrigin,
}

#[derive(Debug, Clone)]
pub struct ContractParam {
    pub name: String,
    pub spec: ContractValueSpec,
}

#[derive(Debug, Clone)]
pub struct FunctionContract {
    pub params: Vec<ContractParam>,
    pub req: TypedExpr,
    #[allow(dead_code)]
    pub req_span: String,
    pub ens: TypedExpr,
    pub ens_span: String,
    pub spec_vars: Vec<String>,
    pub result: ContractValueSpec,
}

#[derive(Debug, Clone)]
pub enum FunctionContractEntry {
    Ready(FunctionContract),
    Invalid(VerificationResult),
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
    pub assertion_contracts: AssertionContracts,
    pub assumption_contracts: AssumptionContracts,
    pub function_contract: Option<FunctionContract>,
    pub spec_vars: Vec<String>,
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

impl AssertionContracts {
    pub fn empty() -> Self {
        Self {
            by_control_point: HashMap::new(),
        }
    }

    pub fn assertion_at(
        &self,
        block: BasicBlock,
        statement_index: usize,
    ) -> Option<&AssertionContract> {
        self.by_control_point.get(&(block, statement_index))
    }
}

impl AssumptionContracts {
    pub fn empty() -> Self {
        Self {
            by_control_point: HashMap::new(),
        }
    }

    pub fn assumption_at(
        &self,
        block: BasicBlock,
        statement_index: usize,
    ) -> Option<&AssumptionContract> {
        self.by_control_point.get(&(block, statement_index))
    }
}

pub fn compute_function_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    skip_def_id: Option<LocalDefId>,
) -> HashMap<LocalDefId, FunctionContractEntry> {
    let mut contracts = HashMap::new();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let ItemKind::Fn { .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        if skip_def_id == Some(def_id) {
            continue;
        }
        let entry = match collect_function_directives(tcx, def_id, item.span) {
            Ok(directives) => {
                let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
                match compute_directives(tcx, def_id, item.span, &body.borrow()) {
                    Ok(prepass) => match prepass.function_contract {
                        Some(contract) => FunctionContractEntry::Ready(contract),
                        None => FunctionContractEntry::Invalid(function_contract_error(
                            tcx,
                            def_id,
                            &tcx.sess
                                .source_map()
                                .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id())),
                            "missing function contract".to_owned(),
                        )),
                    },
                    Err(_) => match build_contract_only(tcx, def_id, &directives.directives) {
                        Ok(contract) => FunctionContractEntry::Ready(contract),
                        Err(err) => FunctionContractEntry::Invalid(err),
                    },
                }
            }
            Err(err) => FunctionContractEntry::Invalid(
                LoopPrepassError {
                    span: err.span,
                    display_span: None,
                    message: err.message,
                }
                .into_verification_result(tcx, def_id),
            ),
        };
        contracts.insert(def_id, entry);
    }
    contracts
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

impl LoopPrepassError {
    fn into_verification_result(self, tcx: TyCtxt<'_>, def_id: LocalDefId) -> VerificationResult {
        VerificationResult {
            function: tcx.def_path_str(def_id.to_def_id()),
            status: VerificationStatus::Unsupported,
            span: self
                .display_span
                .unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(self.span)),
            message: self.message,
        }
    }
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
}

struct ExprResolutionContext<'a> {
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
        (SpecTy::Int, SpecTy::Int) => Ok(SpecTy::Int),
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
        SpecTy::Int => "int".to_owned(),
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
    }
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

fn rust_ty_to_spec_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<SpecTy, String> {
    match ty.kind() {
        TyKind::Bool => Ok(SpecTy::Bool),
        TyKind::Int(_) | TyKind::Uint(_) => Ok(SpecTy::Int),
        TyKind::Ref(_, inner, mutability) => {
            let inner = rust_ty_to_spec_ty(tcx, *inner)?;
            if mutability.is_mut() {
                Ok(SpecTy::Mut(Box::new(inner)))
            } else {
                Ok(SpecTy::Ref(Box::new(inner)))
            }
        }
        TyKind::Tuple(fields) => {
            let mut items = Vec::with_capacity(fields.len());
            for field in fields.iter() {
                items.push(rust_ty_to_spec_ty(tcx, field)?);
            }
            Ok(SpecTy::Tuple(items))
        }
        TyKind::Adt(adt_def, args) if adt_def.is_struct() => {
            let mut items = Vec::new();
            for field in adt_def.non_enum_variant().fields.iter() {
                items.push(rust_ty_to_spec_ty(tcx, field.ty(tcx, args))?);
            }
            Ok(SpecTy::Tuple(items))
        }
        other => Err(format!("unsupported type {other:?}")),
    }
}

fn infer_contract_expr_types(
    expr: &Expr,
    spec_scope: &mut SpecScope,
    params: &HashMap<String, SpecTy>,
    allow_result: bool,
    result_ty: &SpecTy,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(_) => Ok(InferredExprTy::Known(SpecTy::Int)),
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
        Expr::TupleField { base, .. } => {
            let base_ty = infer_contract_expr_types(
                base,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match base_ty {
                InferredExprTy::Known(SpecTy::Tuple(_)) => Ok(InferredExprTy::Unknown),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
                InferredExprTy::Known(other) => Err(format!(
                    "tuple field access requires a tuple, found `{}`",
                    display_spec_ty(&other)
                )),
            }
        }
        Expr::Deref { base } => {
            let base_ty = infer_contract_expr_types(
                base,
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
        Expr::Fin { base } => {
            let base_ty = infer_contract_expr_types(
                base,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            match base_ty {
                InferredExprTy::Known(SpecTy::Mut(inner)) => Ok(InferredExprTy::Known(*inner)),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
                InferredExprTy::Known(other) => Err(format!(
                    "`.fin` requires Mut<T>, found `{}`",
                    display_spec_ty(&other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg_ty = infer_contract_expr_types(
                arg,
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
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::Int)?;
                    Ok(InferredExprTy::Known(SpecTy::Int))
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs_ty = infer_contract_expr_types(
                lhs,
                spec_scope,
                params,
                allow_result,
                result_ty,
                inferred,
            )?;
            let rhs_ty = infer_contract_expr_types(
                rhs,
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
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Int)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Int)?;
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::Add
                | crate::spec::BinaryOp::Sub
                | crate::spec::BinaryOp::Mul => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Int)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Int)?;
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Int))
                }
            }
        }
    }
}

fn infer_body_expr_types<'tcx>(
    expr: &Expr,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
    local_tys: &HashMap<String, SpecTy>,
    inferred: &mut SpecTypeInference,
) -> Result<InferredExprTy, String> {
    match expr {
        Expr::Bool(_) => Ok(InferredExprTy::Known(SpecTy::Bool)),
        Expr::Int(_) => Ok(InferredExprTy::Known(SpecTy::Int)),
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
        Expr::TupleField { base, .. } => {
            let base_ty =
                infer_body_expr_types(expr_base(base), kind, spec_scope, local_tys, inferred)?;
            match base_ty {
                InferredExprTy::Known(SpecTy::Tuple(_)) => Ok(InferredExprTy::Unknown),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
                InferredExprTy::Known(other) => Err(format!(
                    "tuple field access requires a tuple, found `{}`",
                    display_spec_ty(&other)
                )),
            }
        }
        Expr::Deref { base } => {
            let base_ty = infer_body_expr_types(base, kind, spec_scope, local_tys, inferred)?;
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
        Expr::Fin { base } => {
            let base_ty = infer_body_expr_types(base, kind, spec_scope, local_tys, inferred)?;
            match base_ty {
                InferredExprTy::Known(SpecTy::Mut(inner)) => Ok(InferredExprTy::Known(*inner)),
                InferredExprTy::SpecVar(_) | InferredExprTy::Unknown => Ok(InferredExprTy::Unknown),
                InferredExprTy::Known(other) => Err(format!(
                    "`.fin` requires Mut<T>, found `{}`",
                    display_spec_ty(&other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg_ty = infer_body_expr_types(arg, kind, spec_scope, local_tys, inferred)?;
            match op {
                crate::spec::UnaryOp::Not => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::Bool)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::UnaryOp::Neg => {
                    constrain_expr_ty(inferred, &arg_ty, &SpecTy::Int)?;
                    Ok(InferredExprTy::Known(SpecTy::Int))
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs_ty = infer_body_expr_types(lhs, kind, spec_scope, local_tys, inferred)?;
            let rhs_ty = infer_body_expr_types(rhs, kind, spec_scope, local_tys, inferred)?;
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
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Int)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Int)?;
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Bool))
                }
                crate::spec::BinaryOp::Add
                | crate::spec::BinaryOp::Sub
                | crate::spec::BinaryOp::Mul => {
                    constrain_expr_ty(inferred, &lhs_ty, &SpecTy::Int)?;
                    constrain_expr_ty(inferred, &rhs_ty, &SpecTy::Int)?;
                    unify_expr_tys(inferred, &lhs_ty, &rhs_ty)?;
                    Ok(InferredExprTy::Known(SpecTy::Int))
                }
            }
        }
    }
}

fn expr_base(base: &Expr) -> &Expr {
    base
}

fn local_spec_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    resolved: &ResolvedExprEnv,
) -> Result<HashMap<String, SpecTy>, String> {
    let mut types = HashMap::new();
    for (name, local) in &resolved.locals {
        let ty = rust_ty_to_spec_ty(tcx, body.local_decls[*local].ty)?;
        types.insert(name.clone(), ty);
    }
    Ok(types)
}

fn typed_contract_expr(
    expr: &Expr,
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
        Expr::Int(value) => Ok(TypedExpr {
            ty: SpecTy::Int,
            kind: TypedExprKind::Int(*value),
        }),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                let ty = inferred
                    .resolved_ty(name)
                    .ok_or_else(|| format!("could not infer a type for `?{name}`"))?;
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
            let ty = inferred
                .resolved_ty(name)
                .ok_or_else(|| format!("could not infer a type for `?{name}`"))?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::Bind(name.clone()),
            })
        }
        Expr::TupleField { base, index } => {
            let base =
                typed_contract_expr(base, spec_scope, params, allow_result, result_ty, inferred)?;
            let SpecTy::Tuple(items) = &base.ty else {
                return Err(format!(
                    "tuple field access requires a tuple, found `{}`",
                    display_spec_ty(&base.ty)
                ));
            };
            let Some(field_ty) = items.get(*index) else {
                return Err(format!("tuple field .{index} is out of bounds"));
            };
            Ok(TypedExpr {
                ty: field_ty.clone(),
                kind: TypedExprKind::TupleField {
                    base: Box::new(base),
                    index: *index,
                },
            })
        }
        Expr::Deref { base } => {
            let base =
                typed_contract_expr(base, spec_scope, params, allow_result, result_ty, inferred)?;
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
        Expr::Fin { base } => {
            let base =
                typed_contract_expr(base, spec_scope, params, allow_result, result_ty, inferred)?;
            match &base.ty {
                SpecTy::Mut(inner) => Ok(TypedExpr {
                    ty: (**inner).clone(),
                    kind: TypedExprKind::Fin {
                        base: Box::new(base),
                    },
                }),
                other => Err(format!(
                    "`.fin` requires Mut<T>, found `{}`",
                    display_spec_ty(other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg =
                typed_contract_expr(arg, spec_scope, params, allow_result, result_ty, inferred)?;
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
                    if arg.ty != SpecTy::Int {
                        return Err(format!(
                            "unary `-` requires `int`, found `{}`",
                            display_spec_ty(&arg.ty)
                        ));
                    }
                    Ok(TypedExpr {
                        ty: SpecTy::Int,
                        kind: TypedExprKind::Unary {
                            op: *op,
                            arg: Box::new(arg),
                        },
                    })
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs =
                typed_contract_expr(lhs, spec_scope, params, allow_result, result_ty, inferred)?;
            let rhs =
                typed_contract_expr(rhs, spec_scope, params, allow_result, result_ty, inferred)?;
            type_binary_expr(*op, lhs, rhs)
        }
    }
}

fn typed_body_expr(
    expr: &Expr,
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
        Expr::Int(value) => Ok(TypedExpr {
            ty: SpecTy::Int,
            kind: TypedExprKind::Int(*value),
        }),
        Expr::Var(name) => {
            if spec_scope.visible.contains(name) {
                let ty = inferred
                    .resolved_ty(name)
                    .ok_or_else(|| format!("could not infer a type for `?{name}`"))?;
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
            let ty = inferred
                .resolved_ty(name)
                .ok_or_else(|| format!("could not infer a type for `?{name}`"))?;
            Ok(TypedExpr {
                ty,
                kind: TypedExprKind::Bind(name.clone()),
            })
        }
        Expr::TupleField { base, index } => {
            let base = typed_body_expr(expr_base(base), kind, spec_scope, local_tys, inferred)?;
            let SpecTy::Tuple(items) = &base.ty else {
                return Err(format!(
                    "tuple field access requires a tuple, found `{}`",
                    display_spec_ty(&base.ty)
                ));
            };
            let Some(field_ty) = items.get(*index) else {
                return Err(format!("tuple field .{index} is out of bounds"));
            };
            Ok(TypedExpr {
                ty: field_ty.clone(),
                kind: TypedExprKind::TupleField {
                    base: Box::new(base),
                    index: *index,
                },
            })
        }
        Expr::Deref { base } => {
            let base = typed_body_expr(base, kind, spec_scope, local_tys, inferred)?;
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
        Expr::Fin { base } => {
            let base = typed_body_expr(base, kind, spec_scope, local_tys, inferred)?;
            match &base.ty {
                SpecTy::Mut(inner) => Ok(TypedExpr {
                    ty: (**inner).clone(),
                    kind: TypedExprKind::Fin {
                        base: Box::new(base),
                    },
                }),
                other => Err(format!(
                    "`.fin` requires Mut<T>, found `{}`",
                    display_spec_ty(other)
                )),
            }
        }
        Expr::Unary { op, arg } => {
            let arg = typed_body_expr(arg, kind, spec_scope, local_tys, inferred)?;
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
                    if arg.ty != SpecTy::Int {
                        return Err(format!(
                            "unary `-` requires `int`, found `{}`",
                            display_spec_ty(&arg.ty)
                        ));
                    }
                    Ok(TypedExpr {
                        ty: SpecTy::Int,
                        kind: TypedExprKind::Unary {
                            op: *op,
                            arg: Box::new(arg),
                        },
                    })
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs = typed_body_expr(lhs, kind, spec_scope, local_tys, inferred)?;
            let rhs = typed_body_expr(rhs, kind, spec_scope, local_tys, inferred)?;
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
            if lhs.ty != SpecTy::Int || rhs.ty != SpecTy::Int {
                return Err(format!(
                    "comparison requires `int`, found `{}` and `{}`",
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
            if lhs.ty != SpecTy::Int || rhs.ty != SpecTy::Int {
                return Err(format!(
                    "arithmetic requires `int`, found `{}` and `{}`",
                    display_spec_ty(&lhs.ty),
                    display_spec_ty(&rhs.ty)
                ));
            }
            Ok(TypedExpr {
                ty: SpecTy::Int,
                kind: TypedExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            })
        }
    }
}

pub fn compute_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
    body: &Body<'tcx>,
) -> Result<DirectivePrepass, LoopPrepassError> {
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
        .map(|param| (param.name.clone(), param.spec.ty.clone()))
        .collect();
    let result_ty = result.ty.clone();
    if let Some(directive) = req_directive {
        validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            &directive.expr,
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
            DirectiveKind::Assert | DirectiveKind::Assume | DirectiveKind::Inv
        )
    }) {
        let resolution = resolve_expr_env(
            &directive.expr,
            &binding_info,
            &hir_locals,
            directive.span,
            directive_anchor_span(&directive.attach),
            directive.kind,
            &mut body_scope,
        )?;
        resolved_exprs.insert(directive.span_text.clone(), resolution);
    }
    if let Some(directive) = ens_directive {
        validate_function_contract_expr_prepass(
            directive.span,
            &directive.span_text,
            &directive.expr,
            &param_names,
            true,
            &mut contract_scope,
        )?;
    }
    let mut inferred = SpecTypeInference::default();
    let mut contract_infer_scope = SpecScope::default();
    if let Some(directive) = req_directive {
        infer_contract_expr_types(
            &directive.expr,
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
    for directive in directives.directives.iter().filter(|directive| {
        matches!(
            directive.kind,
            DirectiveKind::Assert | DirectiveKind::Assume | DirectiveKind::Inv
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
        infer_body_expr_types(
            &directive.expr,
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
    if let Some(directive) = ens_directive {
        infer_contract_expr_types(
            &directive.expr,
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
            DirectiveKind::Assert | DirectiveKind::Assume | DirectiveKind::Inv
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
        let typed = typed_body_expr(
            &directive.expr,
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
    let typed_ens = match ens_directive {
        Some(directive) => {
            let mut scope = SpecScope::default();
            if let Some(req) = req_directive {
                let _ = typed_contract_expr(
                    &req.expr,
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
            spec_vars: contract_scope.ordered.clone(),
            result,
        }),
        (Some(req), Some(ens)) => Some(FunctionContract {
            params: params.clone(),
            req: typed_req.expect("typed req"),
            req_span: req.span_text.clone(),
            ens: typed_ens.expect("typed ens"),
            ens_span: ens.span_text.clone(),
            spec_vars: contract_scope.ordered.clone(),
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
    let mut assertion_contracts = AssertionContracts::empty();
    let mut assumption_contracts = AssumptionContracts::empty();
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
                if assertion_contracts
                    .by_control_point
                    .insert(
                        control,
                        AssertionContract {
                            assertion: typed_body_exprs
                                .get(&directive.span_text)
                                .cloned()
                                .expect("typed assertion expression"),
                            resolution,
                            assertion_span: directive.span_text.clone(),
                        },
                    )
                    .is_some()
                {
                    return Err(LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message: "multiple //@ assert directives map to the same control point"
                            .to_owned(),
                    });
                }
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
                if assumption_contracts
                    .by_control_point
                    .insert(
                        control,
                        AssumptionContract {
                            assumption: typed_body_exprs
                                .get(&directive.span_text)
                                .cloned()
                                .expect("typed assumption expression"),
                            resolution,
                        },
                    )
                    .is_some()
                {
                    return Err(LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message: "multiple //@ assume directives map to the same control point"
                            .to_owned(),
                    });
                }
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
        }
    }

    Ok(DirectivePrepass {
        directives: lowered,
        loop_contracts,
        assertion_contracts,
        assumption_contracts,
        function_contract,
        spec_vars: body_scope.ordered_with(&contract_scope),
    })
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

fn build_contract_only<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    directives: &[FunctionDirective],
) -> Result<FunctionContract, VerificationResult> {
    let has_manual_contract = directives
        .iter()
        .any(|directive| matches!(directive.kind, DirectiveKind::Req | DirectiveKind::Ens));
    let param_names = if has_manual_contract {
        function_param_names(tcx, def_id)?
    } else {
        function_param_names_relaxed(tcx, def_id)
    };
    let (params, result) =
        function_contract_signature_with_names(tcx, def_id, param_names.clone())?;
    let param_tys: HashMap<_, _> = params
        .iter()
        .map(|param| (param.name.clone(), param.spec.ty.clone()))
        .collect();
    let result_ty = result.ty.clone();
    let mut req = None;
    let mut ens = None;
    let mut validate_scope = SpecScope::default();
    for directive in directives {
        match directive.kind {
            DirectiveKind::Req => {
                if req.is_some() {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        &directive.span_text,
                        "multiple //@ req directives for a function".to_owned(),
                    ));
                }
                validate_contract_expr_core(
                    &directive.expr,
                    &mut validate_scope,
                    &param_names,
                    false,
                )
                .map_err(|message| {
                    function_contract_error(tcx, def_id, &directive.span_text, message)
                })?;
                req = Some(directive);
            }
            DirectiveKind::Ens => {
                if ens.is_some() {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        &directive.span_text,
                        "multiple //@ ens directives for a function".to_owned(),
                    ));
                }
                validate_contract_expr_core(
                    &directive.expr,
                    &mut validate_scope,
                    &param_names,
                    true,
                )
                .map_err(|message| {
                    function_contract_error(tcx, def_id, &directive.span_text, message)
                })?;
                ens = Some(directive);
            }
            _ => {}
        }
    }
    let def_span = tcx
        .sess
        .source_map()
        .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id()));
    match (req, ens) {
        (None, None) => Ok(FunctionContract {
            params,
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
            spec_vars: validate_scope.ordered,
            result,
        }),
        (Some(req), Some(ens)) => {
            let mut inferred = SpecTypeInference::default();
            let mut infer_scope = SpecScope::default();
            infer_contract_expr_types(
                &req.expr,
                &mut infer_scope,
                &param_tys,
                false,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| function_contract_error(tcx, def_id, &req.span_text, message))?;
            infer_contract_expr_types(
                &ens.expr,
                &mut infer_scope,
                &param_tys,
                true,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| function_contract_error(tcx, def_id, &ens.span_text, message))?;

            let mut req_scope = SpecScope::default();
            let typed_req = typed_contract_expr(
                &req.expr,
                &mut req_scope,
                &param_tys,
                false,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| function_contract_error(tcx, def_id, &req.span_text, message))?;
            let typed_ens = typed_contract_expr(
                &ens.expr,
                &mut req_scope,
                &param_tys,
                true,
                &result_ty,
                &mut inferred,
            )
            .map_err(|message| function_contract_error(tcx, def_id, &ens.span_text, message))?;
            Ok(FunctionContract {
                params,
                req: typed_req,
                req_span: req.span_text.clone(),
                ens: typed_ens,
                ens_span: ens.span_text.clone(),
                spec_vars: validate_scope.ordered,
                result,
            })
        }
        _ => Err(function_contract_error(
            tcx,
            def_id,
            &def_span,
            "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        )),
    }
}

fn validate_function_contract_expr_prepass(
    span: Span,
    span_text: &str,
    expr: &Expr,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), LoopPrepassError> {
    validate_contract_expr_core(expr, spec_scope, params, allow_result).map_err(|message| {
        LoopPrepassError {
            span,
            display_span: Some(span_text.to_owned()),
            message,
        }
    })
}

fn validate_contract_expr_core(
    expr: &Expr,
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
        Expr::TupleField { base, .. } | Expr::Deref { base } | Expr::Fin { base } => {
            validate_contract_expr_core(base, spec_scope, params, allow_result)
        }
        Expr::Unary { arg, .. } => {
            validate_contract_expr_core(arg, spec_scope, params, allow_result)
        }
        Expr::Binary { lhs, rhs, .. } => {
            validate_contract_expr_core(lhs, spec_scope, params, allow_result)?;
            validate_contract_expr_core(rhs, spec_scope, params, allow_result)
        }
    }
}

fn resolve_expr_env(
    expr: &Expr,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    kind: DirectiveKind,
    spec_scope: &mut SpecScope,
) -> Result<ResolvedExprEnv, LoopPrepassError> {
    let mut resolved = ResolvedExprEnv::default();
    let mut ctx = ExprResolutionContext {
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
        Expr::TupleField { base, .. } | Expr::Deref { base } | Expr::Fin { base } => {
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
) -> Result<(Vec<ContractParam>, ContractValueSpec), VerificationResult> {
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
            contract_value_spec(tcx, ty)
                .map(|spec| ContractParam { name, spec })
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
    let result = contract_value_spec(tcx, sig.output().skip_binder()).map_err(|message| {
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

pub fn contract_value_spec<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Result<ContractValueSpec, String> {
    let spec_ty = rust_ty_to_spec_ty(tcx, ty)?;
    Ok(match ty.kind() {
        TyKind::Ref(_, inner, mutability) => ContractValueSpec {
            ty: spec_ty,
            invariant: type_invariant_kind(*inner),
            origin: if mutability.is_mut() {
                ContractValueOrigin::Current
            } else {
                ContractValueOrigin::Direct
            },
        },
        _ => ContractValueSpec {
            ty: spec_ty,
            invariant: type_invariant_kind(ty),
            origin: ContractValueOrigin::Direct,
        },
    })
}

fn type_invariant_kind<'tcx>(ty: Ty<'tcx>) -> AutoInvariantKind {
    match ty.kind() {
        TyKind::Int(ty::IntTy::I32) => AutoInvariantKind::I32Range,
        _ => AutoInvariantKind::Trivial,
    }
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
