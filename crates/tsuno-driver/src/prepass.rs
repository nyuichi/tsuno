use std::collections::{BTreeSet, HashMap, VecDeque};

use crate::contracts::{
    HirLoopContract, HirLoopContracts, collect_hir_binding_spans, collect_hir_loop_contracts,
};
use rustc_hir::HirId;
use rustc_middle::mir::{BasicBlock, Body, PlaceElem, Statement, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;

#[derive(Debug, Clone)]
pub struct LoopPrepassError {
    pub span: Span,
    pub basic_block: Option<BasicBlock>,
    pub statement_index: Option<usize>,
    pub message: String,
}

#[derive(Debug, Clone)]
pub struct LoopContract {
    pub header: BasicBlock,
    pub hir_loop_id: HirId,
    pub invariant_block: BasicBlock,
    pub invariant: crate::contracts::SpecExpr,
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
    def_id: LocalDefId,
    body: &Body<'tcx>,
) -> HashMap<HirId, rustc_middle::mir::Local> {
    let hir_binding_spans = collect_hir_binding_spans(tcx, def_id).unwrap_or_default();
    let mut locals = HashMap::new();
    for (local, decl) in body.local_decls.iter_enumerated() {
        let mut matched = None;
        for (hir_id, span) in &hir_binding_spans {
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

fn spans_match<'tcx>(tcx: TyCtxt<'tcx>, left: Span, right: Span) -> bool {
    left == right
        || tcx.sess.source_map().stmt_span(left, right) == right
        || tcx.sess.source_map().stmt_span(right, left) == left
}

pub fn compute_loops<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &Body<'tcx>,
) -> Result<LoopContracts, LoopPrepassError> {
    let hir_loop_contracts = collect_hir_loop_contracts(tcx, def_id)?;
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
                        invariant: crate::contracts::SpecExpr::Bool(true),
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
        let Some((hir_loop_id, invariant_block)) =
            best_loop_contract_for_header(tcx, body, loop_info, &hir_loop_contracts)?
        else {
            return Err(LoopPrepassError {
                span: body.basic_blocks[header].terminator().source_info.span,
                basic_block: Some(header),
                statement_index: None,
                message: format!("loop at bb{} requires tsuno::inv!(..)", header.index()),
            });
        };
        let hir_loop_contract = hir_loop_contracts
            .contract_by_loop_expr_id(hir_loop_id)
            .expect("best_loop_contract_for_header returns collected contract");
        loops
            .get_mut(&header)
            .expect("loop info present")
            .hir_loop_id = hir_loop_id;
        loops
            .get_mut(&header)
            .expect("loop info present")
            .invariant_block = invariant_block;
        loops.get_mut(&header).expect("loop info present").invariant =
            hir_loop_contract.invariant.clone();
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

fn resolve_loop_invariant_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loop_info: &LoopContract,
    hir_loop_contract: &HirLoopContract,
) -> Result<Option<BasicBlock>, LoopPrepassError> {
    let mut candidates = Vec::new();
    for block in &loop_info.body_blocks {
        let data = &body.basic_blocks[*block];
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call { .. } = &term.kind else {
            continue;
        };
        if !spans_match(tcx, term.source_info.span, hir_loop_contract.invariant_span) {
            continue;
        }
        if let Some((stmt_index, stmt)) = data
            .statements
            .iter()
            .enumerate()
            .find(|(_, stmt)| !is_loop_prefix_stmt(tcx, term.source_info.span, stmt))
        {
            return Err(LoopPrepassError {
                span: stmt.source_info.span,
                basic_block: Some(*block),
                statement_index: Some(stmt_index),
                message: "tsuno::inv! is only allowed at the start of a loop body".to_owned(),
            });
        }
        candidates.push(*block);
    }

    let Some(invariant_block) = candidates
        .iter()
        .copied()
        .min_by_key(|block| (loop_entry_distance(body, loop_info, *block), block.index()))
    else {
        return Ok(None);
    };

    Ok(Some(invariant_block))
}

fn best_loop_contract_for_header<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loop_info: &LoopContract,
    hir_loop_contracts: &HirLoopContracts,
) -> Result<Option<(HirId, BasicBlock)>, LoopPrepassError> {
    let mut best: Option<(HirId, BasicBlock, usize)> = None;
    for hir_loop_contract in hir_loop_contracts.by_loop_expr_id.values() {
        let Some(invariant_block) =
            resolve_loop_invariant_block(tcx, body, loop_info, hir_loop_contract)?
        else {
            continue;
        };
        let distance = loop_entry_distance(body, loop_info, invariant_block);
        match best {
            None => {
                best = Some((hir_loop_contract.loop_expr_id, invariant_block, distance));
            }
            Some((_, _, best_distance)) if distance < best_distance => {
                best = Some((hir_loop_contract.loop_expr_id, invariant_block, distance));
            }
            _ => {}
        }
    }
    if let Some((hir_loop_id, invariant_block, _)) = best {
        return Ok(Some((hir_loop_id, invariant_block)));
    }

    let mut detail = String::new();
    let _ = std::fmt::Write::write_fmt(
        &mut detail,
        format_args!(
            "header bb{} could not be matched to a loop contract\n",
            loop_info.header.index()
        ),
    );
    for block in &loop_info.body_blocks {
        let data = &body.basic_blocks[*block];
        let _ = std::fmt::Write::write_fmt(
            &mut detail,
            format_args!(
                "  bb{} term={}\n",
                block.index(),
                tcx.sess
                    .source_map()
                    .span_to_diagnostic_string(data.terminator().source_info.span)
            ),
        );
    }
    for hir_loop_contract in hir_loop_contracts.by_loop_expr_id.values() {
        let _ = std::fmt::Write::write_fmt(
            &mut detail,
            format_args!(
                "  contract {:?} inv_span={}\n",
                hir_loop_contract.loop_expr_id,
                tcx.sess
                    .source_map()
                    .span_to_diagnostic_string(hir_loop_contract.invariant_span)
            ),
        );
    }
    Err(LoopPrepassError {
        span: body.basic_blocks[loop_info.header]
            .terminator()
            .source_info
            .span,
        basic_block: Some(loop_info.header),
        statement_index: None,
        message: detail,
    })
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

fn is_loop_prefix_stmt<'tcx>(tcx: TyCtxt<'tcx>, call_span: Span, stmt: &Statement<'tcx>) -> bool {
    matches!(
        stmt.kind,
        StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Nop
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. }
    ) || stmt.source_info.span.from_expansion()
        || tcx
            .sess
            .source_map()
            .stmt_span(stmt.source_info.span, call_span)
            == call_span
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
