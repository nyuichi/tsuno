use std::collections::HashMap;
use std::ops::ControlFlow;

use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Block, Expr, ExprKind, HirId, LoopSource, MatchSource, Stmt, StmtKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};
use syn::{BinOp as SynBinOp, Expr as SynExpr, Lit as SynLit, LitStr, UnOp as SynUnOp};

use crate::prepass::{HirBindingInfo, LoopPrepassError};

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
    pub loop_span: Span,
    pub body_span: Span,
    pub body_block_id: HirId,
    pub invariant: SpecExpr,
    pub invariant_span: Span,
}

#[derive(Debug, Clone)]
pub struct HirLoopContracts {
    pub by_loop_expr_id: HashMap<HirId, HirLoopContract>,
}

impl HirLoopContracts {
    pub fn empty() -> Self {
        Self {
            by_loop_expr_id: HashMap::new(),
        }
    }
}

pub fn collect_hir_loop_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    binding_info: &HirBindingInfo,
) -> Result<HirLoopContracts, LoopPrepassError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut collector = HirLoopContractCollector {
        tcx,
        contracts: HashMap::new(),
        binding_info,
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => Ok(HirLoopContracts {
            by_loop_expr_id: collector.contracts,
        }),
        ControlFlow::Break(err) => Err(err),
    }
}

struct HirLoopContractCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    contracts: HashMap<HirId, HirLoopContract>,
    binding_info: &'a HirBindingInfo,
}

impl<'a, 'tcx> HirLoopContractCollector<'a, 'tcx> {
    fn collect_loop_contract(
        &mut self,
        loop_expr: &'tcx Expr<'tcx>,
        body: &'tcx Block<'tcx>,
        source: LoopSource,
    ) -> Result<(), LoopPrepassError> {
        let loop_body = self.loop_body_block(loop_expr, body, source)?;
        let entry_span = body_entry_span(loop_body);
        let (invariant, invariant_span) =
            self.collect_loop_invariant(loop_expr, loop_body, entry_span)?;
        let contract = HirLoopContract {
            loop_expr_id: loop_expr.hir_id,
            loop_span: loop_expr.span,
            body_span: loop_body.span,
            body_block_id: loop_body.hir_id,
            invariant,
            invariant_span,
        };
        self.contracts.insert(loop_expr.hir_id, contract);
        Ok(())
    }

    fn collect_loop_invariant(
        &self,
        loop_expr: &'tcx Expr<'tcx>,
        body: &'tcx Block<'tcx>,
        entry_span: Span,
    ) -> Result<(SpecExpr, Span), LoopPrepassError> {
        let loop_source = self
            .tcx
            .sess
            .source_map()
            .span_to_snippet(loop_expr.span)
            .map_err(|_| self.missing_invariant_error(loop_expr, body))?;
        let body_source = self
            .tcx
            .sess
            .source_map()
            .span_to_snippet(body.span)
            .map_err(|_| self.missing_invariant_error(loop_expr, body))?;
        let Some(body_index) = loop_source.find(&body_source) else {
            return Err(self.missing_invariant_error(loop_expr, body));
        };
        let prefix_source = &loop_source[..body_index];
        let invariant_count = prefix_source.matches("//@ inv").count();
        if invariant_count == 0 {
            return Err(self.missing_invariant_error(loop_expr, body));
        }
        if invariant_count > 1 {
            return Err(self.multiple_invariant_error(entry_span));
        }

        let Some(directive_pos) = prefix_source.rfind("//@ inv") else {
            return Err(self.missing_invariant_error(loop_expr, body));
        };

        let line_end = prefix_source[directive_pos..]
            .find('\n')
            .map(|idx| directive_pos + idx)
            .unwrap_or(prefix_source.len());
        let directive_line =
            prefix_source[directive_pos..line_end].trim_end_matches(['\r', ' ', '\t']);
        let after_line = &prefix_source[line_end..];
        let Some(after_newline) = after_line.strip_prefix('\n') else {
            return Err(self.invariant_position_error(entry_span));
        };
        if after_newline.contains('\n') {
            return Err(self.invariant_position_error(entry_span));
        }
        if !after_newline
            .chars()
            .all(|c| matches!(c, ' ' | '\t' | '\r'))
        {
            return Err(self.invariant_position_error(entry_span));
        }

        let predicate_text = directive_line
            .strip_prefix("//@ inv")
            .expect("directive line starts with //@ inv")
            .trim();
        let lit = syn::parse_str::<LitStr>(predicate_text).map_err(|err| LoopPrepassError {
            span: entry_span,
            basic_block: None,
            statement_index: None,
            message: format!("failed to parse //@ inv predicate: {err}"),
        })?;
        let expr = parse_inv_template(&lit).map_err(|err| LoopPrepassError {
            span: entry_span,
            basic_block: None,
            statement_index: None,
            message: err.to_string(),
        })?;
        let invariant = self.lower_syn_spec_expr(&expr, entry_span, entry_span)?;
        Ok((invariant, entry_span))
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
                "loop body starting at {} requires exactly one //@ inv \"...\" before the body",
                self.tcx
                    .sess
                    .source_map()
                    .span_to_diagnostic_string(body.span)
            ),
        }
    }

    fn multiple_invariant_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "loop header may contain exactly one //@ inv before the body".to_owned(),
        }
    }

    fn invariant_position_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "//@ inv must be placed immediately before the loop body".to_owned(),
        }
    }

    fn unsupported_loop_shape_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "unsupported loop desugaring shape for //@ inv".to_owned(),
        }
    }

    fn lower_syn_spec_expr(
        &self,
        expr: &SynExpr,
        span: Span,
        anchor_span: Span,
    ) -> Result<SpecExpr, LoopPrepassError> {
        match expr {
            SynExpr::Lit(lit) => match &lit.lit {
                SynLit::Bool(value) => Ok(SpecExpr::Bool(value.value)),
                SynLit::Int(value) => {
                    let value = value.base10_parse::<i64>().map_err(|_| LoopPrepassError {
                        span,
                        basic_block: None,
                        statement_index: None,
                        message: "integer literal in //@ inv is too large".to_owned(),
                    })?;
                    Ok(SpecExpr::Int(value))
                }
                _ => Err(self
                    .unsupported_syn_spec_expr(span, "unsupported literal in //@ inv predicate")),
            },
            SynExpr::Path(path) => {
                let Some(ident) = path.path.get_ident() else {
                    return Err(self
                        .unsupported_syn_spec_expr(span, "unsupported path in //@ inv predicate"));
                };
                let name = Symbol::intern(&ident.to_string());
                let Some(hir_id) = self.resolve_binding_hir_id(name, anchor_span) else {
                    return Err(LoopPrepassError {
                        span,
                        basic_block: None,
                        statement_index: None,
                        message: format!("unresolved binding `{ident}` in //@ inv"),
                    });
                };
                Ok(SpecExpr::Var { hir_id, name })
            }
            SynExpr::Unary(expr) => {
                let op = match expr.op {
                    SynUnOp::Not(_) => SpecUnaryOp::Not,
                    SynUnOp::Neg(_) => SpecUnaryOp::Neg,
                    _ => {
                        return Err(self.unsupported_syn_spec_expr(
                            span,
                            "unsupported unary operator in //@ inv predicate",
                        ));
                    }
                };
                Ok(SpecExpr::Unary {
                    op,
                    arg: Box::new(self.lower_syn_spec_expr(&expr.expr, span, anchor_span)?),
                })
            }
            SynExpr::Binary(expr) => {
                let op = match expr.op {
                    SynBinOp::Add(_) => SpecBinaryOp::Add,
                    SynBinOp::Sub(_) => SpecBinaryOp::Sub,
                    SynBinOp::Mul(_) => SpecBinaryOp::Mul,
                    SynBinOp::Eq(_) => SpecBinaryOp::Eq,
                    SynBinOp::Ne(_) => SpecBinaryOp::Ne,
                    SynBinOp::Gt(_) => SpecBinaryOp::Gt,
                    SynBinOp::Ge(_) => SpecBinaryOp::Ge,
                    SynBinOp::Lt(_) => SpecBinaryOp::Lt,
                    SynBinOp::Le(_) => SpecBinaryOp::Le,
                    SynBinOp::And(_) => SpecBinaryOp::And,
                    SynBinOp::Or(_) => SpecBinaryOp::Or,
                    _ => {
                        return Err(self.unsupported_syn_spec_expr(
                            span,
                            "unsupported binary operator in //@ inv predicate",
                        ));
                    }
                };
                Ok(SpecExpr::Binary {
                    op,
                    lhs: Box::new(self.lower_syn_spec_expr(&expr.left, span, anchor_span)?),
                    rhs: Box::new(self.lower_syn_spec_expr(&expr.right, span, anchor_span)?),
                })
            }
            SynExpr::Paren(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span),
            SynExpr::Group(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span),
            SynExpr::Reference(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span),
            SynExpr::Cast(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span),
            SynExpr::Block(expr) => {
                let Some(syn::Stmt::Expr(inner, None)) = expr.block.stmts.last() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        "block without a trailing expression is unsupported in //@ inv",
                    ));
                };
                self.lower_syn_spec_expr(inner, span, anchor_span)
            }
            SynExpr::Call(_) | SynExpr::MethodCall(_) => Err(self.unsupported_syn_spec_expr(
                span,
                "function calls are unsupported in //@ inv predicates",
            )),
            _ => {
                Err(self
                    .unsupported_syn_spec_expr(span, "unsupported expression in //@ inv predicate"))
            }
        }
    }

    fn resolve_binding_hir_id(&self, name: Symbol, anchor_span: Span) -> Option<HirId> {
        self.binding_info.by_name.get(&name).and_then(|bindings| {
            bindings
                .iter()
                .filter(|(_, span)| span.lo() < anchor_span.lo())
                .max_by_key(|(_, span)| span.lo())
                .map(|(hir_id, _)| *hir_id)
        })
    }

    fn unsupported_syn_spec_expr(
        &self,
        span: Span,
        message: impl Into<String>,
    ) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: message.into(),
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for HirLoopContractCollector<'a, 'tcx> {
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

fn stmt_expr<'tcx>(stmt: &'tcx Stmt<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    match stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => Some(expr),
        StmtKind::Let(_) | StmtKind::Item(_) => None,
    }
}

fn body_entry_span(body: &Block<'_>) -> Span {
    body.stmts
        .first()
        .map(|stmt| stmt.span)
        .or_else(|| body.expr.map(|expr| expr.span))
        .unwrap_or(body.span)
}

fn parse_inv_template(lit: &LitStr) -> syn::Result<SynExpr> {
    let raw = lit.value();
    let mut output = String::new();
    let mut chars = raw.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '{' => {
                if chars.peek() == Some(&'{') {
                    chars.next();
                    output.push('{');
                    continue;
                }

                let mut inner = String::new();
                let mut closed = false;
                while let Some(next) = chars.next() {
                    if next == '}' {
                        if chars.peek() == Some(&'}') {
                            chars.next();
                            inner.push('}');
                            continue;
                        }
                        closed = true;
                        break;
                    }
                    inner.push(next);
                }
                if !closed {
                    return Err(syn::Error::new(
                        lit.span(),
                        "unclosed `{` in //@ inv template",
                    ));
                }
                let inner = inner.trim();
                if inner.is_empty() {
                    return Err(syn::Error::new(
                        lit.span(),
                        "empty interpolation in //@ inv template",
                    ));
                }
                output.push('(');
                output.push_str(inner);
                output.push(')');
            }
            '}' => {
                if chars.peek() == Some(&'}') {
                    chars.next();
                    output.push('}');
                } else {
                    return Err(syn::Error::new(
                        lit.span(),
                        "unmatched `}` in //@ inv template",
                    ));
                }
            }
            _ => output.push(ch),
        }
    }

    syn::parse_str::<SynExpr>(&output).map_err(|err| {
        syn::Error::new(
            lit.span(),
            format!("failed to parse //@ inv predicate: {err}"),
        )
    })
}
