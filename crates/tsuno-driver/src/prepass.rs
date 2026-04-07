use std::collections::{BTreeSet, HashMap, VecDeque};
use std::ops::ControlFlow;

use crate::contracts::{
    SpecBinaryOp, SpecExpr as HirSpecExpr, SpecUnaryOp, collect_hir_assertions,
    collect_hir_loop_contracts,
};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{HirId, Pat, PatKind};
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
pub struct LoopPrepassError {
    pub span: Span,
    pub basic_block: Option<BasicBlock>,
    pub statement_index: Option<usize>,
    pub message: String,
}

#[derive(Debug, Clone)]
pub enum MirSpecExpr {
    Bool(bool),
    Int(i64),
    Var(Local),
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
    pub invariant_span: Span,
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
    pub assertion_span: Span,
}

#[derive(Debug, Clone)]
pub struct AssertionContracts {
    pub by_control_point: HashMap<(BasicBlock, usize), AssertionContract>,
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
                        invariant_span: body.basic_blocks[header].terminator().source_info.span,
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
                basic_block: Some(header),
                statement_index: None,
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
        let invariant = lower_hir_spec_expr(
            &hir_loop_contract.invariant,
            &hir_locals,
            hir_loop_contract.invariant_span,
        )?;
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
            .invariant_span = hir_loop_contract.invariant_span;
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
                basic_block: None,
                statement_index: None,
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
            hir_assertion.assertion_span,
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
                basic_block: Some(basic_block),
                statement_index: Some(statement_index),
                message: "multiple //@ assert directives map to the same control point".to_owned(),
            });
        }
    }
    Ok(AssertionContracts { by_control_point })
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
                    basic_block: None,
                    statement_index: None,
                    message: format!("missing MIR local for HIR id {:?}", hir_id),
                });
            };
            Ok(MirSpecExpr::Var(local))
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
