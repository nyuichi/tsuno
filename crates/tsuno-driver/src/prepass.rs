use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::ops::ControlFlow;

use crate::directive::{
    CollectedFunctionDirectives, DirectiveAttach, DirectiveError, DirectiveKind, FunctionDirective,
    collect_function_directives,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::Expr;
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
    pub prophecies: HashMap<String, Local>,
    pub spec_vars: HashSet<String>,
}

#[derive(Debug, Clone)]
pub struct LoopContract {
    pub header: BasicBlock,
    pub hir_loop_id: HirId,
    pub invariant_block: BasicBlock,
    pub invariant: Expr,
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
    pub assertion: Expr,
    pub resolution: ResolvedExprEnv,
    pub assertion_span: String,
}

#[derive(Debug, Clone)]
pub struct AssertionContracts {
    pub by_control_point: HashMap<(BasicBlock, usize), AssertionContract>,
}

#[derive(Debug, Clone)]
pub struct AssumptionContract {
    pub assumption: Expr,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContractValueSpec {
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
    pub req: Expr,
    #[allow(dead_code)]
    pub req_span: String,
    pub ens: Expr,
    pub ens_span: String,
    pub spec_vars: Vec<String>,
    pub result: ContractValueSpec,
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
) -> HashMap<LocalDefId, FunctionContract> {
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
        let Ok(directives) = collect_function_directives(tcx, def_id, item.span) else {
            continue;
        };
        let Ok(contract) = build_function_contract(tcx, def_id, &directives.directives) else {
            continue;
        };
        contracts.insert(def_id, contract);
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
    let def_span = tcx
        .sess
        .source_map()
        .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id()));
    let function_contract = match (req_directive, ens_directive) {
        (None, None) => Some(FunctionContract {
            params: params.clone(),
            req: Expr::Bool(true),
            req_span: def_span.clone(),
            ens: Expr::Bool(true),
            ens_span: def_span,
            spec_vars: contract_scope.ordered.clone(),
            result,
        }),
        (Some(req), Some(ens)) => Some(FunctionContract {
            params: params.clone(),
            req: req.expr.clone(),
            req_span: req.span_text.clone(),
            ens: ens.expr.clone(),
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
    let loop_contracts = collect_loop_contracts(tcx, body, &directives, &resolved_exprs)?;
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
                            assertion: directive.expr.clone(),
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
                            assumption: directive.expr.clone(),
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
                        invariant: Expr::Bool(true),
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
        loop_contract.invariant = directive.expr.clone();
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

fn build_function_contract<'tcx>(
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
    let mut req = None;
    let mut ens = None;
    let mut spec_scope = SpecScope::default();
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
                validate_function_contract_expr(
                    tcx,
                    def_id,
                    &directive.expr,
                    &directive.span_text,
                    &param_names,
                    false,
                    &mut spec_scope,
                )?;
                req = Some((directive.expr.clone(), directive.span_text.clone()));
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
                validate_function_contract_expr(
                    tcx,
                    def_id,
                    &directive.expr,
                    &directive.span_text,
                    &param_names,
                    true,
                    &mut spec_scope,
                )?;
                ens = Some((directive.expr.clone(), directive.span_text.clone()));
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
            req: Expr::Bool(true),
            req_span: def_span.clone(),
            ens: Expr::Bool(true),
            ens_span: def_span,
            spec_vars: spec_scope.ordered,
            result,
        }),
        (Some((req, req_span)), Some((ens, ens_span))) => Ok(FunctionContract {
            params,
            req,
            req_span,
            ens,
            ens_span,
            spec_vars: spec_scope.ordered,
            result,
        }),
        _ => Err(function_contract_error(
            tcx,
            def_id,
            &tcx.sess
                .source_map()
                .span_to_diagnostic_string(tcx.def_span(def_id.to_def_id())),
            "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        )),
    }
}

fn validate_function_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    expr: &Expr,
    span: &str,
    params: &[String],
    allow_result: bool,
    spec_scope: &mut SpecScope,
) -> Result<(), VerificationResult> {
    validate_contract_expr_core(expr, spec_scope, params, allow_result)
        .map_err(|message| function_contract_error(tcx, def_id, span, message))
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
        Expr::Prophecy(name) => {
            if params.iter().any(|param| param == name) {
                Ok(())
            } else {
                Err(format!(
                    "unresolved prophecy binding `{name}` in function contract"
                ))
            }
        }
        Expr::Field { base, .. } => {
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
        Expr::Prophecy(name) => {
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
            resolved.prophecies.insert(name.clone(), local);
            Ok(())
        }
        Expr::Field { base, .. } => resolve_expr_env_into(base, ctx, resolved),
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
        .map(|(name, ty)| ContractParam {
            name,
            spec: contract_value_spec(ty),
        })
        .collect();
    Ok((params, contract_value_spec(sig.output().skip_binder())))
}

fn contract_value_spec<'tcx>(ty: Ty<'tcx>) -> ContractValueSpec {
    match ty.kind() {
        TyKind::Ref(_, inner, mutability) => ContractValueSpec {
            invariant: type_invariant_kind(*inner),
            origin: if mutability.is_mut() {
                ContractValueOrigin::Current
            } else {
                ContractValueOrigin::Direct
            },
        },
        _ => ContractValueSpec {
            invariant: type_invariant_kind(ty),
            origin: ContractValueOrigin::Direct,
        },
    }
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
