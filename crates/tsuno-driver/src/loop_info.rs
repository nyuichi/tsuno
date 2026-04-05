use std::collections::{BTreeSet, HashMap};

use rustc_middle::mir::{BasicBlock, Body, PlaceElem, StatementKind, TerminatorKind};

#[derive(Debug, Clone)]
pub struct LoopInfo {
    pub header: BasicBlock,
    pub body_blocks: BTreeSet<BasicBlock>,
    pub exit_blocks: BTreeSet<BasicBlock>,
    pub written_locals: BTreeSet<rustc_middle::mir::Local>,
}

pub fn compute_loops<'tcx>(body: &Body<'tcx>) -> HashMap<BasicBlock, LoopInfo> {
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
                        body_blocks,
                        exit_blocks,
                        written_locals,
                    });
            }
        }
    }
    loops
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
