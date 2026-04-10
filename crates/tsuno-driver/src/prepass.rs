use std::collections::{BTreeSet, HashMap, VecDeque};
use std::ops::ControlFlow;

use crate::directive::{
    CollectedFunctionDirectives, DirectiveAttach, DirectiveError, DirectiveKind, FunctionDirective,
    collect_function_directives,
};
use crate::report::{VerificationResult, VerificationStatus};
use crate::spec::{BinaryOp, Expr, UnaryOp};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{HirId, ItemKind, Pat, PatKind};
use rustc_middle::mir::{BasicBlock, Body, Local, PlaceElem, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};

#[derive(Debug, Clone, Default)]
pub struct HirBindingInfo {
    pub spans: HashMap<HirId, Span>,
    pub by_name: HashMap<Symbol, Vec<(HirId, Span)>>,
}

#[derive(Debug, Clone)]
pub enum MirSpecExpr {
    Bool(bool),
    Int(i64),
    Var(Local),
    #[allow(dead_code)]
    Prophecy(Local),
    Field {
        base: Box<MirSpecExpr>,
        index: usize,
    },
    Unary {
        op: UnaryOp,
        arg: Box<MirSpecExpr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<MirSpecExpr>,
        rhs: Box<MirSpecExpr>,
    },
}

#[derive(Debug, Clone)]
pub struct LoopContract {
    pub header: BasicBlock,
    pub hir_loop_id: HirId,
    pub invariant_block: BasicBlock,
    pub invariant: MirSpecExpr,
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
    pub assertion: MirSpecExpr,
    pub assertion_span: String,
}

#[derive(Debug, Clone)]
pub struct AssertionContracts {
    pub by_control_point: HashMap<(BasicBlock, usize), AssertionContract>,
}

#[derive(Debug, Clone)]
pub struct AssumptionContract {
    pub assumption: MirSpecExpr,
}

#[derive(Debug, Clone)]
pub struct AssumptionContracts {
    pub by_control_point: HashMap<(BasicBlock, usize), AssumptionContract>,
}

#[derive(Debug, Clone)]
pub struct FunctionContract {
    pub params: Vec<String>,
    pub req: Expr,
    #[allow(dead_code)]
    pub req_span: String,
    pub ens: Expr,
    pub ens_span: String,
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
) -> Result<HashMap<LocalDefId, FunctionContract>, VerificationResult> {
    let mut contracts = HashMap::new();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let ItemKind::Fn { .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        let directives = collect_function_directives(tcx, def_id, item.span)
            .map_err(|err| directive_error_to_verification_result(tcx, def_id, err))?;
        let Some(contract) = build_function_contract(tcx, def_id, &directives.directives)? else {
            continue;
        };
        contracts.insert(def_id, contract);
    }
    Ok(contracts)
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
    let function_contract = build_function_contract_prepass(tcx, def_id, &directives.directives)?;
    let loop_contracts =
        collect_loop_contracts(tcx, body, &directives, &binding_info, &hir_locals)?;
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
                let assertion = lower_spec_expr_to_mir(
                    &directive.expr,
                    &binding_info,
                    &hir_locals,
                    directive.span,
                    directive_anchor_span(&directive.attach),
                    directive.kind,
                )?;
                if assertion_contracts
                    .by_control_point
                    .insert(
                        control,
                        AssertionContract {
                            assertion,
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
                let assumption = lower_spec_expr_to_mir(
                    &directive.expr,
                    &binding_info,
                    &hir_locals,
                    directive.span,
                    directive_anchor_span(&directive.attach),
                    directive.kind,
                )?;
                if assumption_contracts
                    .by_control_point
                    .insert(control, AssumptionContract { assumption })
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
    })
}

fn directive_error_to_prepass(err: DirectiveError) -> LoopPrepassError {
    LoopPrepassError {
        span: err.span,
        display_span: None,
        message: err.message,
    }
}

fn directive_error_to_verification_result(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    err: DirectiveError,
) -> VerificationResult {
    VerificationResult {
        function: tcx.def_path_str(def_id.to_def_id()),
        status: VerificationStatus::Unsupported,
        span: tcx.sess.source_map().span_to_diagnostic_string(err.span),
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
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
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
                        invariant: MirSpecExpr::Bool(true),
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
        let header_span = body.basic_blocks[header].terminator().source_info.span;
        let entry_span = loop_entry_anchor_span(body, loop_info).unwrap_or(header_span);
        let invariant_block = loop_info
            .body_blocks
            .iter()
            .copied()
            .filter(|block| *block != header)
            .min_by_key(|block| (loop_entry_distance(body, loop_info, *block), block.index()))
            .unwrap_or(header);
        let invariant = lower_spec_expr_to_mir(
            &directive.expr,
            binding_info,
            hir_locals,
            directive.span,
            entry_span,
            DirectiveKind::Inv,
        )?;
        let loop_contract = loops.get_mut(&header).expect("loop info present");
        loop_contract.hir_loop_id = loop_expr_id;
        loop_contract.invariant_block = invariant_block;
        loop_contract.invariant = invariant;
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
) -> Result<Option<FunctionContract>, VerificationResult> {
    let mut req = None;
    let mut ens = None;
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
                    &directive.span_text,
                    "req",
                    &directive.expr,
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
                    &directive.span_text,
                    "ens",
                    &directive.expr,
                )?;
                ens = Some((directive.expr.clone(), directive.span_text.clone()));
            }
            _ => {}
        }
    }

    match (req, ens) {
        (None, None) => Ok(None),
        (Some((req, req_span)), Some((ens, ens_span))) => Ok(Some(FunctionContract {
            params: function_param_names(tcx, def_id)?,
            req,
            req_span,
            ens,
            ens_span,
        })),
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

fn build_function_contract_prepass(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    directives: &[FunctionDirective],
) -> Result<Option<FunctionContract>, LoopPrepassError> {
    let mut req = None;
    let mut ens = None;
    for directive in directives {
        match directive.kind {
            DirectiveKind::Req => {
                if req.is_some() {
                    return Err(LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message: "multiple //@ req directives for a function".to_owned(),
                    });
                }
                validate_function_contract_expr_prepass(
                    directive.span,
                    &directive.span_text,
                    "req",
                    &directive.expr,
                )?;
                req = Some((directive.expr.clone(), directive.span_text.clone()));
            }
            DirectiveKind::Ens => {
                if ens.is_some() {
                    return Err(LoopPrepassError {
                        span: directive.span,
                        display_span: Some(directive.span_text.clone()),
                        message: "multiple //@ ens directives for a function".to_owned(),
                    });
                }
                validate_function_contract_expr_prepass(
                    directive.span,
                    &directive.span_text,
                    "ens",
                    &directive.expr,
                )?;
                ens = Some((directive.expr.clone(), directive.span_text.clone()));
            }
            _ => {}
        }
    }
    match (req, ens) {
        (None, None) => Ok(None),
        (Some((req, req_span)), Some((ens, ens_span))) => Ok(Some(FunctionContract {
            params: function_param_names(tcx, def_id).map_err(|err| LoopPrepassError {
                span: tcx.def_span(def_id.to_def_id()),
                display_span: None,
                message: err.message,
            })?,
            req,
            req_span,
            ens,
            ens_span,
        })),
        _ => Err(LoopPrepassError {
            span: tcx.def_span(def_id.to_def_id()),
            display_span: None,
            message: "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        }),
    }
}

fn validate_function_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: &str,
    kind: &str,
    expr: &Expr,
) -> Result<(), VerificationResult> {
    match expr {
        Expr::Result if kind != "ens" => Err(function_contract_error(
            tcx,
            def_id,
            span,
            "`result` is only supported in //@ ens predicates".to_owned(),
        )),
        Expr::Field { base, .. } => validate_function_contract_expr(tcx, def_id, span, kind, base),
        Expr::Unary { arg, .. } => validate_function_contract_expr(tcx, def_id, span, kind, arg),
        Expr::Binary { lhs, rhs, .. } => {
            validate_function_contract_expr(tcx, def_id, span, kind, lhs)?;
            validate_function_contract_expr(tcx, def_id, span, kind, rhs)
        }
        _ => Ok(()),
    }
}

fn validate_function_contract_expr_prepass(
    span: Span,
    span_text: &str,
    kind: &str,
    expr: &Expr,
) -> Result<(), LoopPrepassError> {
    match expr {
        Expr::Result if kind != "ens" => Err(LoopPrepassError {
            span,
            display_span: Some(span_text.to_owned()),
            message: "`result` is only supported in //@ ens predicates".to_owned(),
        }),
        Expr::Field { base, .. } => {
            validate_function_contract_expr_prepass(span, span_text, kind, base)
        }
        Expr::Unary { arg, .. } => {
            validate_function_contract_expr_prepass(span, span_text, kind, arg)
        }
        Expr::Binary { lhs, rhs, .. } => {
            validate_function_contract_expr_prepass(span, span_text, kind, lhs)?;
            validate_function_contract_expr_prepass(span, span_text, kind, rhs)
        }
        _ => Ok(()),
    }
}

fn lower_spec_expr_to_mir(
    expr: &Expr,
    binding_info: &HirBindingInfo,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
    anchor_span: Span,
    kind: DirectiveKind,
) -> Result<MirSpecExpr, LoopPrepassError> {
    match expr {
        Expr::Bool(value) => Ok(MirSpecExpr::Bool(*value)),
        Expr::Int(value) => Ok(MirSpecExpr::Int(*value)),
        Expr::Var(name) => {
            let symbol = Symbol::intern(name);
            let Some(hir_id) = resolve_binding_hir_id(binding_info, symbol, anchor_span) else {
                return Err(LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!("unresolved binding `{name}` in //@ {}", kind.keyword()),
                });
            };
            let Some(local) = hir_locals.get(&hir_id).copied() else {
                return Err(LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("missing MIR local for HIR id {:?}", hir_id),
                });
            };
            Ok(MirSpecExpr::Var(local))
        }
        Expr::Result => Err(LoopPrepassError {
            span,
            display_span: None,
            message: "`result` is only supported in //@ ens predicates".to_owned(),
        }),
        Expr::Prophecy(name) => {
            let symbol = Symbol::intern(name);
            let Some(hir_id) = resolve_binding_hir_id(binding_info, symbol, anchor_span) else {
                return Err(LoopPrepassError {
                    span,
                    display_span: None,
                    message: format!("unresolved binding `{name}` in //@ {}", kind.keyword()),
                });
            };
            let Some(local) = hir_locals.get(&hir_id).copied() else {
                return Err(LoopPrepassError {
                    span: anchor_span,
                    display_span: None,
                    message: format!("missing MIR local for HIR id {:?}", hir_id),
                });
            };
            Ok(MirSpecExpr::Prophecy(local))
        }
        Expr::Field { base, index } => Ok(MirSpecExpr::Field {
            base: Box::new(lower_spec_expr_to_mir(
                base,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                kind,
            )?),
            index: *index,
        }),
        Expr::Unary { op, arg } => Ok(MirSpecExpr::Unary {
            op: *op,
            arg: Box::new(lower_spec_expr_to_mir(
                arg,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                kind,
            )?),
        }),
        Expr::Binary { op, lhs, rhs } => Ok(MirSpecExpr::Binary {
            op: *op,
            lhs: Box::new(lower_spec_expr_to_mir(
                lhs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                kind,
            )?),
            rhs: Box::new(lower_spec_expr_to_mir(
                rhs,
                binding_info,
                hir_locals,
                span,
                anchor_span,
                kind,
            )?),
        }),
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
