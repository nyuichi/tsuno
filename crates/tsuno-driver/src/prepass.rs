use std::collections::{BTreeSet, HashMap, VecDeque};

use rustc_middle::mir::{BasicBlock, Body, PlaceElem, Statement, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

#[derive(Debug, Clone)]
pub struct LoopPrepassError {
    pub span: Span,
    pub basic_block: Option<BasicBlock>,
    pub statement_index: Option<usize>,
    pub message: String,
}

#[derive(Debug, Clone)]
pub struct LoopInfo {
    pub header: BasicBlock,
    pub invariant_block: BasicBlock,
    pub body_blocks: BTreeSet<BasicBlock>,
    pub exit_blocks: BTreeSet<BasicBlock>,
    pub written_locals: BTreeSet<rustc_middle::mir::Local>,
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

pub fn compute_loops<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Result<HashMap<BasicBlock, LoopInfo>, LoopPrepassError> {
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
                    .and_modify(|info: &mut LoopInfo| {
                        info.body_blocks.extend(body_blocks.iter().copied());
                        info.exit_blocks.extend(exit_blocks.iter().copied());
                        info.written_locals.extend(written_locals.iter().copied());
                    })
                    .or_insert(LoopInfo {
                        header,
                        invariant_block: header,
                        body_blocks,
                        exit_blocks,
                        written_locals,
                    });
            }
        }
    }

    let headers: Vec<_> = loops.keys().copied().collect();
    for header in headers {
        let invariant_block = resolve_loop_invariant_block(tcx, body, &loops[&header])?;
        loops
            .get_mut(&header)
            .expect("loop info present")
            .invariant_block = invariant_block;
    }

    Ok(loops)
}

fn resolve_loop_invariant_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loop_info: &LoopInfo,
) -> Result<BasicBlock, LoopPrepassError> {
    let mut candidates = Vec::new();
    for block in &loop_info.body_blocks {
        let data = &body.basic_blocks[*block];
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, .. } = &term.kind else {
            continue;
        };
        if !is_marker_call(tcx, func, "__tsuno_invariant") {
            continue;
        }
        let call_span = term.source_info.span;
        if let Some((stmt_index, stmt)) = data
            .statements
            .iter()
            .enumerate()
            .find(|(_, stmt)| !is_loop_prefix_stmt(tcx, call_span, stmt))
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
        return Err(LoopPrepassError {
            span: body.basic_blocks[loop_info.header]
                .terminator()
                .source_info
                .span,
            basic_block: Some(loop_info.header),
            statement_index: None,
            message: format!(
                "loop at bb{} requires tsuno::inv!(..)",
                loop_info.header.index()
            ),
        });
    };

    Ok(invariant_block)
}

fn loop_entry_distance<'tcx>(body: &Body<'tcx>, loop_info: &LoopInfo, target: BasicBlock) -> usize {
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

fn is_marker_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &rustc_middle::mir::Operand<'tcx>,
    suffix: &str,
) -> bool {
    let Some(def_id) = call_target_def_id(operand) else {
        return false;
    };
    tcx.def_path_str(def_id).contains(suffix)
}

fn call_target_def_id<'tcx>(
    operand: &rustc_middle::mir::Operand<'tcx>,
) -> Option<rustc_span::def_id::DefId> {
    let rustc_middle::mir::Operand::Constant(constant) = operand else {
        return None;
    };
    let rustc_middle::ty::TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
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
