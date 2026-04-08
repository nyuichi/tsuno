use std::collections::{BTreeSet, HashMap, VecDeque};
use std::ops::ControlFlow;

use crate::directive::{
    FunctionContractSource, SpecBinaryOp, SpecExpr as HirSpecExpr, SpecUnaryOp,
    collect_function_contract_source, collect_hir_assertions, collect_hir_loop_contracts,
};
use crate::report::{VerificationResult, VerificationStatus};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{HirId, ItemKind, Pat, PatKind};
use rustc_middle::mir::{BasicBlock, Body, Local, PlaceElem, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};
use syn::{Expr as SynExpr, Lit};

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
    Unary {
        op: SpecUnaryOp,
        arg: Box<MirSpecExpr>,
    },
    Binary {
        op: SpecBinaryOp,
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
pub struct FunctionContract {
    pub params: Vec<String>,
    pub req: ContractExpr,
    #[allow(dead_code)]
    pub req_span: String,
    pub ens: ContractExpr,
    pub ens_span: String,
}

#[derive(Debug, Clone)]
pub enum ContractExpr {
    Bool(bool),
    Int(i64),
    Var(String),
    Prophecy(String),
    Unary {
        op: SpecUnaryOp,
        arg: Box<ContractExpr>,
    },
    Binary {
        op: SpecBinaryOp,
        lhs: Box<ContractExpr>,
        rhs: Box<ContractExpr>,
    },
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
        let Some(source_contract) = collect_function_contract_source(tcx, def_id, item.span)?
        else {
            continue;
        };
        let contract = lower_function_contract(tcx, def_id, source_contract)?;
        contracts.insert(def_id, contract);
    }
    Ok(contracts)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SwitchJoin {
    pub join_block: BasicBlock,
}

pub fn compute_switch_joins<'tcx>(body: &Body<'tcx>) -> HashMap<BasicBlock, SwitchJoin> {
    let successors: Vec<Vec<usize>> = body
        .basic_blocks
        .iter_enumerated()
        .map(|(_, data)| {
            data.terminator()
                .successors()
                .map(|bb| bb.index())
                .collect()
        })
        .collect();
    let joins = compute_switch_joins_from_successors(&successors);
    joins
        .into_iter()
        .map(|(bb, join)| {
            (
                BasicBlock::from_usize(bb),
                SwitchJoin {
                    join_block: BasicBlock::from_usize(join),
                },
            )
        })
        .collect()
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
    pub message: String,
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

pub fn compute_loops<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
) -> Result<LoopContracts, LoopPrepassError> {
    let binding_info = collect_hir_binding_info(tcx, def_id)?;
    let hir_loop_contracts = collect_hir_loop_contracts(tcx, def_id, &binding_info)?;
    let hir_locals = compute_hir_locals(tcx, body, &binding_info);
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
    for header in headers {
        let loop_info = &loops[&header];
        let header_span = body.basic_blocks[header].terminator().source_info.span;
        let entry_span = loop_entry_anchor_span(body, loop_info).unwrap_or(header_span);
        let Some(hir_loop_contract) =
            hir_loop_contracts
                .by_loop_expr_id
                .values()
                .find(|contract| {
                    span_contains(contract.loop_span, header_span)
                        || span_contains(contract.body_span, entry_span)
                })
        else {
            return Err(LoopPrepassError {
                span: header_span,
                message: format!(
                    "loop at bb{} requires exactly one //@ inv before the body",
                    header.index()
                ),
            });
        };
        let invariant_block = loop_info
            .body_blocks
            .iter()
            .copied()
            .filter(|block| *block != header)
            .min_by_key(|block| (loop_entry_distance(body, loop_info, *block), block.index()))
            .unwrap_or(header);
        let invariant =
            lower_hir_spec_expr(&hir_loop_contract.invariant, &hir_locals, header_span)?;
        loops
            .get_mut(&header)
            .expect("loop info present")
            .hir_loop_id = hir_loop_contract.loop_expr_id;
        loops
            .get_mut(&header)
            .expect("loop info present")
            .invariant_block = invariant_block;
        loops.get_mut(&header).expect("loop info present").invariant = invariant;
        loops
            .get_mut(&header)
            .expect("loop info present")
            .invariant_span = hir_loop_contract.invariant_span.clone();
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

pub fn compute_assertions<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
) -> Result<AssertionContracts, LoopPrepassError> {
    let binding_info = collect_hir_binding_info(tcx, def_id)?;
    let hir_assertions = collect_hir_assertions(tcx, def_id, &binding_info)?;
    let hir_locals = compute_hir_locals(tcx, body, &binding_info);
    let mut by_control_point = HashMap::new();
    for hir_assertion in hir_assertions.items {
        let target = control_point_after(body, hir_assertion.stmt_span);
        let Some((basic_block, statement_index)) = target else {
            return Err(LoopPrepassError {
                span: hir_assertion.stmt_span,
                message: format!(
                    "unable to map //@ assert at {} to MIR",
                    tcx.sess
                        .source_map()
                        .span_to_diagnostic_string(hir_assertion.stmt_span)
                ),
            });
        };
        let assertion = lower_hir_spec_expr(
            &hir_assertion.assertion,
            &hir_locals,
            hir_assertion.stmt_span,
        )?;
        if by_control_point
            .insert(
                (basic_block, statement_index),
                AssertionContract {
                    assertion,
                    assertion_span: hir_assertion.assertion_span,
                },
            )
            .is_some()
        {
            return Err(LoopPrepassError {
                span: hir_assertion.stmt_span,
                message: "multiple //@ assert directives map to the same control point".to_owned(),
            });
        }
    }
    Ok(AssertionContracts { by_control_point })
}

fn lower_function_contract<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    source: FunctionContractSource,
) -> Result<FunctionContract, VerificationResult> {
    Ok(FunctionContract {
        params: function_param_names(tcx, def_id)?,
        req: lower_function_contract_expr(tcx, def_id, &source.req_span, "req", &source.req)?,
        ens: lower_function_contract_expr(tcx, def_id, &source.ens_span, "ens", &source.ens)?,
        req_span: source.req_span,
        ens_span: source.ens_span,
    })
}

fn lower_function_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: &str,
    kind: &str,
    expr: &SynExpr,
) -> Result<ContractExpr, VerificationResult> {
    match expr {
        SynExpr::Lit(lit) => match &lit.lit {
            Lit::Bool(value) => Ok(ContractExpr::Bool(value.value)),
            Lit::Int(value) => Ok(ContractExpr::Int(value.base10_parse::<i64>().map_err(
                |err| {
                    function_contract_error(
                        tcx,
                        def_id,
                        span,
                        format!("integer literal in //@ {kind} is too large: {err}"),
                    )
                },
            )?)),
            _ => Err(function_contract_error(
                tcx,
                def_id,
                span,
                format!("unsupported literal in //@ {kind} predicate"),
            )),
        },
        SynExpr::Path(path) => {
            let Some(ident) = path.path.get_ident() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported path in //@ {kind} predicate"),
                ));
            };
            let name = ident.to_string();
            if name == "result" {
                if kind != "ens" {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        span,
                        "`result` is only supported in //@ ens predicates".to_owned(),
                    ));
                }
                return Ok(ContractExpr::Var(name));
            }
            Ok(ContractExpr::Var(name))
        }
        SynExpr::Call(expr) => {
            let SynExpr::Path(path) = expr.func.as_ref() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported call in //@ {kind} predicate"),
                ));
            };
            let Some(ident) = path.path.get_ident() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported call in //@ {kind} predicate"),
                ));
            };
            if ident != "__prophecy" || expr.args.len() != 1 {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported call in //@ {kind} predicate"),
                ));
            }
            let Some(SynExpr::Path(arg_path)) = expr.args.first() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported prophecy argument in //@ {kind} predicate"),
                ));
            };
            let Some(arg_ident) = arg_path.path.get_ident() else {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    span,
                    format!("unsupported prophecy argument in //@ {kind} predicate"),
                ));
            };
            Ok(ContractExpr::Prophecy(arg_ident.to_string()))
        }
        SynExpr::Unary(expr) => {
            let op = match expr.op {
                syn::UnOp::Not(_) => SpecUnaryOp::Not,
                syn::UnOp::Neg(_) => SpecUnaryOp::Neg,
                _ => {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        span,
                        format!("unsupported unary operator in //@ {kind} predicate"),
                    ));
                }
            };
            Ok(ContractExpr::Unary {
                op,
                arg: Box::new(lower_function_contract_expr(
                    tcx, def_id, span, kind, &expr.expr,
                )?),
            })
        }
        SynExpr::Binary(expr) => {
            let op = match expr.op {
                syn::BinOp::Add(_) => SpecBinaryOp::Add,
                syn::BinOp::Sub(_) => SpecBinaryOp::Sub,
                syn::BinOp::Mul(_) => SpecBinaryOp::Mul,
                syn::BinOp::Eq(_) => SpecBinaryOp::Eq,
                syn::BinOp::Ne(_) => SpecBinaryOp::Ne,
                syn::BinOp::Gt(_) => SpecBinaryOp::Gt,
                syn::BinOp::Ge(_) => SpecBinaryOp::Ge,
                syn::BinOp::Lt(_) => SpecBinaryOp::Lt,
                syn::BinOp::Le(_) => SpecBinaryOp::Le,
                syn::BinOp::And(_) => SpecBinaryOp::And,
                syn::BinOp::Or(_) => SpecBinaryOp::Or,
                _ => {
                    return Err(function_contract_error(
                        tcx,
                        def_id,
                        span,
                        format!("unsupported binary operator in //@ {kind} predicate"),
                    ));
                }
            };
            Ok(ContractExpr::Binary {
                op,
                lhs: Box::new(lower_function_contract_expr(
                    tcx, def_id, span, kind, &expr.left,
                )?),
                rhs: Box::new(lower_function_contract_expr(
                    tcx,
                    def_id,
                    span,
                    kind,
                    &expr.right,
                )?),
            })
        }
        SynExpr::Paren(expr) => lower_function_contract_expr(tcx, def_id, span, kind, &expr.expr),
        SynExpr::Group(expr) => lower_function_contract_expr(tcx, def_id, span, kind, &expr.expr),
        SynExpr::Reference(expr) => {
            lower_function_contract_expr(tcx, def_id, span, kind, &expr.expr)
        }
        SynExpr::Cast(expr) => lower_function_contract_expr(tcx, def_id, span, kind, &expr.expr),
        _ => Err(function_contract_error(
            tcx,
            def_id,
            span,
            format!("unsupported expression in //@ {kind} predicate"),
        )),
    }
}

fn lower_hir_spec_expr(
    expr: &HirSpecExpr,
    hir_locals: &HashMap<HirId, Local>,
    span: Span,
) -> Result<MirSpecExpr, LoopPrepassError> {
    match expr {
        HirSpecExpr::Bool(value) => Ok(MirSpecExpr::Bool(*value)),
        HirSpecExpr::Int(value) => Ok(MirSpecExpr::Int(*value)),
        HirSpecExpr::Var { hir_id, .. } => {
            let Some(local) = hir_locals.get(hir_id).copied() else {
                return Err(LoopPrepassError {
                    span,
                    message: format!("missing MIR local for HIR id {:?}", hir_id),
                });
            };
            Ok(MirSpecExpr::Var(local))
        }
        HirSpecExpr::Prophecy { hir_id, .. } => {
            let Some(local) = hir_locals.get(hir_id).copied() else {
                return Err(LoopPrepassError {
                    span,
                    message: format!("missing MIR local for HIR id {:?}", hir_id),
                });
            };
            Ok(MirSpecExpr::Prophecy(local))
        }
        HirSpecExpr::Unary { op, arg } => Ok(MirSpecExpr::Unary {
            op: *op,
            arg: Box::new(lower_hir_spec_expr(arg, hir_locals, span)?),
        }),
        HirSpecExpr::Binary { op, lhs, rhs } => Ok(MirSpecExpr::Binary {
            op: *op,
            lhs: Box::new(lower_hir_spec_expr(lhs, hir_locals, span)?),
            rhs: Box::new(lower_hir_spec_expr(rhs, hir_locals, span)?),
        }),
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

fn compute_switch_joins_from_successors(successors: &[Vec<usize>]) -> HashMap<usize, usize> {
    let ipostdom = compute_immediate_postdominators(successors);
    let mut joins = HashMap::new();
    for (bb, targets) in successors.iter().enumerate() {
        if targets.len() > 1
            && let Some(join) = ipostdom[bb]
        {
            joins.insert(bb, join);
        }
    }
    joins
}

fn compute_immediate_postdominators(successors: &[Vec<usize>]) -> Vec<Option<usize>> {
    let exit = successors.len();
    let universe: BTreeSet<usize> = (0..=exit).collect();
    let mut postdoms = vec![universe.clone(); successors.len() + 1];
    postdoms[exit] = BTreeSet::from([exit]);

    let mut changed = true;
    while changed {
        changed = false;
        for bb in (0..successors.len()).rev() {
            let mut targets = successors[bb].clone();
            if targets.is_empty() {
                targets.push(exit);
            }
            let mut next = universe.clone();
            for succ in targets {
                next = next.intersection(&postdoms[succ]).copied().collect();
            }
            next.insert(bb);
            if next != postdoms[bb] {
                postdoms[bb] = next;
                changed = true;
            }
        }
    }

    (0..successors.len())
        .map(|bb| {
            let candidates: Vec<_> = postdoms[bb]
                .iter()
                .copied()
                .filter(|id| *id != bb)
                .collect();
            candidates.iter().copied().find(|candidate| {
                candidates
                    .iter()
                    .copied()
                    .filter(|other| other != candidate)
                    .all(|other| postdoms[*candidate].contains(&other))
            })
        })
        .collect()
}
