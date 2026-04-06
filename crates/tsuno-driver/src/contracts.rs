use std::collections::HashMap;
use std::ops::ControlFlow;

use rustc_ast::LitKind;
use rustc_hir::def::Res;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    BinOpKind, Block, Expr, ExprKind, HirId, Lit, LoopSource, MatchSource, Pat, PatKind, QPath,
    Stmt, StmtKind, UnOp,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;

use crate::prepass::LoopPrepassError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecExpr {
    Bool(bool),
    Int(i64),
    Var {
        hir_id: HirId,
        name: rustc_span::Symbol,
    },
    Unary {
        op: SpecUnaryOp,
        arg: Box<SpecExpr>,
    },
    Binary {
        op: SpecBinaryOp,
        lhs: Box<SpecExpr>,
        rhs: Box<SpecExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecUnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecBinaryOp {
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    And,
    Or,
}

#[derive(Debug, Clone)]
pub struct HirLoopContract {
    pub loop_expr_id: HirId,
    pub body_block_id: HirId,
    pub invariant: SpecExpr,
    pub invariant_span: Span,
}

#[derive(Debug, Clone)]
pub struct HirLoopContracts {
    pub by_loop_expr_id: HashMap<HirId, HirLoopContract>,
    pub body_block_to_loop_expr_id: HashMap<HirId, HirId>,
}

impl HirLoopContracts {
    pub fn empty() -> Self {
        Self {
            by_loop_expr_id: HashMap::new(),
            body_block_to_loop_expr_id: HashMap::new(),
        }
    }

    pub fn contract_by_loop_expr_id(&self, loop_expr_id: HirId) -> Option<&HirLoopContract> {
        self.by_loop_expr_id.get(&loop_expr_id)
    }

    pub fn canonical_loop_expr_id(&self, hir_id: HirId) -> Option<HirId> {
        self.by_loop_expr_id
            .contains_key(&hir_id)
            .then_some(hir_id)
            .or_else(|| self.body_block_to_loop_expr_id.get(&hir_id).copied())
    }
}

pub fn collect_hir_loop_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Result<HirLoopContracts, LoopPrepassError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut collector = HirLoopContractCollector {
        tcx,
        contracts: HashMap::new(),
        body_block_to_loop_expr_id: HashMap::new(),
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => Ok(HirLoopContracts {
            by_loop_expr_id: collector.contracts,
            body_block_to_loop_expr_id: collector.body_block_to_loop_expr_id,
        }),
        ControlFlow::Break(err) => Err(err),
    }
}

pub fn collect_hir_binding_spans<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Result<HashMap<HirId, Span>, LoopPrepassError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut collector = HirBindingSpanCollector {
        spans: HashMap::new(),
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => Ok(collector.spans),
        ControlFlow::Break(err) => Err(err),
    }
}

struct HirLoopContractCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    contracts: HashMap<HirId, HirLoopContract>,
    body_block_to_loop_expr_id: HashMap<HirId, HirId>,
}

struct HirBindingSpanCollector {
    spans: HashMap<HirId, Span>,
}

impl<'tcx> HirLoopContractCollector<'tcx> {
    fn collect_loop_contract(
        &mut self,
        loop_expr: &'tcx Expr<'tcx>,
        body: &'tcx Block<'tcx>,
        source: LoopSource,
    ) -> Result<(), LoopPrepassError> {
        let loop_body = self.loop_body_block(loop_expr, body, source)?;
        let (invariant, invariant_span) = self.collect_loop_invariant(loop_expr, loop_body)?;
        let contract = HirLoopContract {
            loop_expr_id: loop_expr.hir_id,
            body_block_id: loop_body.hir_id,
            invariant,
            invariant_span,
        };
        self.body_block_to_loop_expr_id
            .insert(body.hir_id, loop_expr.hir_id);
        self.body_block_to_loop_expr_id
            .insert(loop_body.hir_id, loop_expr.hir_id);
        self.contracts.insert(loop_expr.hir_id, contract);
        Ok(())
    }

    fn collect_loop_invariant(
        &self,
        loop_expr: &'tcx Expr<'tcx>,
        body: &'tcx Block<'tcx>,
    ) -> Result<(SpecExpr, Span), LoopPrepassError> {
        for stmt in body.stmts {
            if is_prefix_stmt(stmt) {
                continue;
            }
            if let Some(invocation) = self.direct_invocation_from_stmt(stmt)? {
                return Ok(invocation);
            }
            return Err(self.invocation_position_error(stmt.span));
        }
        if let Some(expr) = body.expr
            && let Some(invocation) = self.direct_invocation_from_expr(expr)?
        {
            return Ok(invocation);
        }
        Err(self.missing_invariant_error(loop_expr, body))
    }

    fn loop_body_block(
        &self,
        loop_expr: &'tcx Expr<'tcx>,
        body: &'tcx Block<'tcx>,
        source: LoopSource,
    ) -> Result<&'tcx Block<'tcx>, LoopPrepassError> {
        match source {
            LoopSource::Loop => Ok(body.innermost_block()),
            LoopSource::While => {
                let control_expr = self
                    .first_loop_control_expr(body)
                    .ok_or_else(|| self.missing_invariant_error(loop_expr, body))?;
                let control_expr = control_expr.peel_blocks().peel_drop_temps();
                let ExprKind::If(_, then, _) = control_expr.kind else {
                    return Err(self.unsupported_loop_shape_error(control_expr.span));
                };
                let ExprKind::Block(then_block, _) = then.peel_blocks().kind else {
                    return Err(self.unsupported_loop_shape_error(then.span));
                };
                Ok(then_block.innermost_block())
            }
            LoopSource::ForLoop => {
                let control_expr = self
                    .first_loop_control_expr(body)
                    .ok_or_else(|| self.missing_invariant_error(loop_expr, body))?;
                let control_expr = control_expr.peel_blocks().peel_drop_temps();
                let ExprKind::Match(_, arms, MatchSource::ForLoopDesugar) = control_expr.kind
                else {
                    return Err(self.unsupported_loop_shape_error(control_expr.span));
                };
                for arm in arms {
                    let arm_body = arm.body.peel_blocks().peel_drop_temps();
                    if let ExprKind::Block(block, _) = arm_body.kind {
                        return Ok(block.innermost_block());
                    }
                }
                Err(self.unsupported_loop_shape_error(control_expr.span))
            }
        }
    }

    fn first_loop_control_expr(&self, body: &'tcx Block<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        if let Some(expr) = body.expr {
            return Some(expr);
        }
        body.stmts.iter().find_map(stmt_expr)
    }

    fn direct_invocation_from_stmt(
        &self,
        stmt: &'tcx Stmt<'tcx>,
    ) -> Result<Option<(SpecExpr, Span)>, LoopPrepassError> {
        match stmt.kind {
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => self.direct_invocation_from_expr(expr),
            StmtKind::Let(_) | StmtKind::Item(_) => Ok(None),
        }
    }

    fn direct_invocation_from_expr(
        &self,
        expr: &'tcx Expr<'tcx>,
    ) -> Result<Option<(SpecExpr, Span)>, LoopPrepassError> {
        if let Some(invocation) = self.invocation_from_expr(expr)? {
            return Ok(Some(invocation));
        }
        let expr = expr.peel_drop_temps();
        match expr.kind {
            ExprKind::Block(block, _) => {
                if !expr.span.from_expansion() {
                    return Ok(None);
                }
                for stmt in block.stmts {
                    if is_prefix_stmt(stmt) {
                        continue;
                    }
                    if let Some(invocation) = self.direct_invocation_from_stmt(stmt)? {
                        return Ok(Some(invocation));
                    }
                    return Ok(None);
                }
                if let Some(inner) = block.expr {
                    self.invocation_from_expr(inner)
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn invocation_from_expr(
        &self,
        expr: &'tcx Expr<'tcx>,
    ) -> Result<Option<(SpecExpr, Span)>, LoopPrepassError> {
        let expr = expr.peel_blocks().peel_drop_temps();
        let ExprKind::Call(fun, args) = expr.kind else {
            return Ok(None);
        };
        if !self.is_invocation_callee(fun) {
            return Ok(None);
        }
        if args.len() != 1 {
            return Err(LoopPrepassError {
                span: expr.span,
                basic_block: None,
                statement_index: None,
                message: "tsuno::inv! expects exactly one predicate".to_owned(),
            });
        }
        let predicate = lower_spec_expr(self.tcx, &args[0])?;
        Ok(Some((predicate, expr.span)))
    }

    fn is_invocation_callee(&self, expr: &'tcx Expr<'tcx>) -> bool {
        let expr = expr.peel_blocks().peel_drop_temps();
        let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind else {
            return false;
        };
        let Res::Def(_, def_id) = path.res else {
            return false;
        };
        self.tcx.def_path_str(def_id).contains("__tsuno_invariant")
    }

    fn invocation_position_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "tsuno::inv! is only allowed at the start of a loop body".to_owned(),
        }
    }

    fn missing_invariant_error(
        &self,
        loop_expr: &'tcx Expr<'tcx>,
        body: &'tcx Block<'tcx>,
    ) -> LoopPrepassError {
        LoopPrepassError {
            span: loop_expr.span,
            basic_block: None,
            statement_index: None,
            message: format!(
                "loop body starting at {} requires tsuno::inv!(..)",
                self.tcx
                    .sess
                    .source_map()
                    .span_to_diagnostic_string(body.span)
            ),
        }
    }

    fn unsupported_loop_shape_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "unsupported loop desugaring shape for tsuno::inv!".to_owned(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for HirLoopContractCollector<'tcx> {
    type NestedFilter = intravisit::nested_filter::None;
    type Result = ControlFlow<LoopPrepassError>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Self::Result {
        if let ExprKind::Loop(body, _, source, _) = expr.kind
            && let Err(err) = self.collect_loop_contract(expr, body, source)
        {
            return ControlFlow::Break(err);
        }
        intravisit::walk_expr(self, expr)
    }
}

impl<'tcx> Visitor<'tcx> for HirBindingSpanCollector {
    type NestedFilter = intravisit::nested_filter::None;
    type Result = ControlFlow<LoopPrepassError>;

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) -> Self::Result {
        if let PatKind::Binding(..) = pat.kind {
            self.spans.entry(pat.hir_id).or_insert(pat.span);
        }
        intravisit::walk_pat(self, pat)
    }
}

fn is_prefix_stmt(stmt: &Stmt<'_>) -> bool {
    matches!(stmt.kind, StmtKind::Item(_) | StmtKind::Let(_))
}

fn stmt_expr<'tcx>(stmt: &'tcx Stmt<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    match stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => Some(expr),
        StmtKind::Let(_) | StmtKind::Item(_) => None,
    }
}

fn lower_spec_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Result<SpecExpr, LoopPrepassError> {
    let expr = expr.peel_blocks().peel_drop_temps();
    match expr.kind {
        ExprKind::Lit(Lit { node, .. }) => match node {
            LitKind::Bool(value) => Ok(SpecExpr::Bool(value)),
            LitKind::Int(value, _) => {
                let value = i64::try_from(value.get()).map_err(|_| LoopPrepassError {
                    span: expr.span,
                    basic_block: None,
                    statement_index: None,
                    message: "integer literal in tsuno::inv! is too large".to_owned(),
                })?;
                Ok(SpecExpr::Int(value))
            }
            _ => Err(unsupported_spec_expr(
                expr.span,
                "unsupported literal in tsuno::inv! predicate",
            )),
        },
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir_id) => Ok(SpecExpr::Var {
                hir_id,
                name: path
                    .segments
                    .last()
                    .expect("local path has a segment")
                    .ident
                    .name,
            }),
            Res::Def(_, def_id) => Err(unsupported_spec_expr(
                expr.span,
                format!(
                    "unsupported path in tsuno::inv!: {}",
                    tcx.def_path_str(def_id)
                ),
            )),
            _ => Err(unsupported_spec_expr(
                expr.span,
                "unsupported path in tsuno::inv! predicate",
            )),
        },
        ExprKind::Unary(op, inner) => {
            let op = match op {
                UnOp::Not => SpecUnaryOp::Not,
                UnOp::Neg => SpecUnaryOp::Neg,
                _ => {
                    return Err(unsupported_spec_expr(
                        expr.span,
                        "unsupported unary operator in tsuno::inv! predicate",
                    ));
                }
            };
            Ok(SpecExpr::Unary {
                op,
                arg: Box::new(lower_spec_expr(tcx, inner)?),
            })
        }
        ExprKind::Binary(op, lhs, rhs) => {
            let op = match op.node {
                BinOpKind::Add => SpecBinaryOp::Add,
                BinOpKind::Sub => SpecBinaryOp::Sub,
                BinOpKind::Mul => SpecBinaryOp::Mul,
                BinOpKind::Eq => SpecBinaryOp::Eq,
                BinOpKind::Ne => SpecBinaryOp::Ne,
                BinOpKind::Gt => SpecBinaryOp::Gt,
                BinOpKind::Ge => SpecBinaryOp::Ge,
                BinOpKind::Lt => SpecBinaryOp::Lt,
                BinOpKind::Le => SpecBinaryOp::Le,
                BinOpKind::And => SpecBinaryOp::And,
                BinOpKind::Or => SpecBinaryOp::Or,
                _ => {
                    return Err(unsupported_spec_expr(
                        expr.span,
                        "unsupported binary operator in tsuno::inv! predicate",
                    ));
                }
            };
            Ok(SpecExpr::Binary {
                op,
                lhs: Box::new(lower_spec_expr(tcx, lhs)?),
                rhs: Box::new(lower_spec_expr(tcx, rhs)?),
            })
        }
        ExprKind::Use(inner, _) | ExprKind::Type(inner, _) | ExprKind::Cast(inner, _) => {
            lower_spec_expr(tcx, inner)
        }
        ExprKind::Block(block, _) => {
            if let Some(inner) = block.expr {
                lower_spec_expr(tcx, inner)
            } else {
                Err(unsupported_spec_expr(
                    expr.span,
                    "block without a trailing expression is unsupported in tsuno::inv!",
                ))
            }
        }
        ExprKind::DropTemps(inner) => lower_spec_expr(tcx, inner),
        ExprKind::Err(_) => Err(unsupported_spec_expr(
            expr.span,
            "invalid expression in tsuno::inv! predicate",
        )),
        ExprKind::Call(..) | ExprKind::MethodCall(..) => Err(unsupported_spec_expr(
            expr.span,
            "function calls are unsupported in tsuno::inv! predicates",
        )),
        _ => Err(unsupported_spec_expr(
            expr.span,
            "unsupported expression in tsuno::inv! predicate",
        )),
    }
}

fn unsupported_spec_expr(span: Span, message: impl Into<String>) -> LoopPrepassError {
    LoopPrepassError {
        span,
        basic_block: None,
        statement_index: None,
        message: message.into(),
    }
}
