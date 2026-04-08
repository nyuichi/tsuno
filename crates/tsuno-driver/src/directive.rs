use std::collections::HashMap;
use std::ops::ControlFlow;

use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Block, Expr, ExprKind, HirId, LoopSource, MatchSource, Stmt, StmtKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};
use syn::{BinOp as SynBinOp, Expr as SynExpr, Lit as SynLit, LitStr, UnOp as SynUnOp};

use crate::prepass::{HirBindingInfo, LoopPrepassError};
use crate::report::{VerificationResult, VerificationStatus};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecExpr {
    Bool(bool),
    Int(i64),
    Var {
        hir_id: HirId,
        name: rustc_span::Symbol,
    },
    Prophecy {
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
    pub invariant: SpecExpr,
    pub invariant_span: String,
}

#[derive(Debug, Clone)]
pub struct HirLoopContracts {
    pub by_loop_expr_id: HashMap<HirId, HirLoopContract>,
}

#[derive(Debug, Clone)]
pub struct HirAssertionContract {
    pub stmt_span: Span,
    pub assertion: SpecExpr,
    pub assertion_span: String,
}

#[derive(Debug, Clone)]
pub struct HirAssertionContracts {
    pub items: Vec<HirAssertionContract>,
}

#[derive(Clone)]
pub(crate) struct FunctionContractSource {
    pub(crate) req: SynExpr,
    pub(crate) req_span: String,
    pub(crate) ens: SynExpr,
    pub(crate) ens_span: String,
}

pub fn collect_hir_loop_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    binding_info: &HirBindingInfo,
) -> Result<HirLoopContracts, LoopPrepassError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut collector = HirLoopContractCollector {
        lowerer: SpecExprLowerer { tcx, binding_info },
        contracts: HashMap::new(),
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => Ok(HirLoopContracts {
            by_loop_expr_id: collector.contracts,
        }),
        ControlFlow::Break(err) => Err(err),
    }
}

pub fn collect_hir_assertions<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    binding_info: &HirBindingInfo,
) -> Result<HirAssertionContracts, LoopPrepassError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut collector = HirAssertionCollector {
        lowerer: SpecExprLowerer { tcx, binding_info },
        assertions: Vec::new(),
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => Ok(HirAssertionContracts {
            items: collector.assertions,
        }),
        ControlFlow::Break(err) => Err(err),
    }
}

pub fn has_verify_marker(tcx: TyCtxt<'_>, span: Span) -> bool {
    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
    let Some(source) = loc.file.src.as_deref() else {
        return false;
    };
    verify_marker_in_source(source, loc.line)
}

fn display_line_span(file_name: &str, line_no: usize, line_text: &str) -> String {
    let start_col = line_text.chars().take_while(|c| c.is_whitespace()).count() + 1;
    let end_col = start_col + line_text.trim_end().chars().count();
    format!("{file_name}:{line_no}:{start_col}: {line_no}:{end_col}")
}

pub(crate) fn collect_function_contract_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
) -> Result<Option<FunctionContractSource>, VerificationResult> {
    let loc = tcx.sess.source_map().lookup_char_pos(item_span.lo());
    let Some(source) = loc.file.src.as_deref() else {
        return Ok(None);
    };
    let Some(lines) = function_contract_lines_before_item(source, loc.line) else {
        return Ok(None);
    };

    let mut req = None;
    let mut req_span = None;
    let mut ens = None;
    let mut ens_span = None;
    let mut saw_contract = false;
    let file_name = loc.file.name.prefer_local().to_string();
    let block_start_line = loc.line - lines.len();
    for (index, line) in lines.iter().enumerate() {
        let line_no = block_start_line + index;
        let raw_line = source.lines().nth(line_no - 1).unwrap_or(line).trim_end();
        if let Some(rest) = line.strip_prefix("//@ req") {
            if req.is_some() {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    item_span,
                    "multiple //@ req directives for a function".to_owned(),
                ));
            }
            saw_contract = true;
            req = Some(parse_function_contract_expr(
                tcx,
                def_id,
                item_span,
                "req",
                rest.trim(),
            )?);
            req_span = Some(display_line_span(&file_name, line_no, raw_line));
        } else if let Some(rest) = line.strip_prefix("//@ ens") {
            if ens.is_some() {
                return Err(function_contract_error(
                    tcx,
                    def_id,
                    item_span,
                    "multiple //@ ens directives for a function".to_owned(),
                ));
            }
            saw_contract = true;
            ens = Some(parse_function_contract_expr(
                tcx,
                def_id,
                item_span,
                "ens",
                rest.trim(),
            )?);
            ens_span = Some(display_line_span(&file_name, line_no, raw_line));
        }
    }

    if !saw_contract {
        return Ok(None);
    }

    let req = req.ok_or_else(|| {
        function_contract_error(
            tcx,
            def_id,
            item_span,
            "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        )
    })?;
    let req_span =
        req_span.unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(item_span));
    let ens = ens.ok_or_else(|| {
        function_contract_error(
            tcx,
            def_id,
            item_span,
            "function contract requires exactly one //@ req and one //@ ens".to_owned(),
        )
    })?;
    let ens_span =
        ens_span.unwrap_or_else(|| tcx.sess.source_map().span_to_diagnostic_string(item_span));
    Ok(Some(FunctionContractSource {
        req,
        req_span,
        ens,
        ens_span,
    }))
}

pub(crate) fn function_contract_lines_before_item(
    source: &str,
    item_line: usize,
) -> Option<Vec<String>> {
    if item_line <= 1 {
        return None;
    }

    let lines: Vec<_> = source.lines().collect();
    let mut idx = item_line.saturating_sub(2);
    let mut block = Vec::new();
    while let Some(line) = lines.get(idx) {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            break;
        }
        if !trimmed.starts_with("//@") {
            break;
        }
        block.push(trimmed.to_owned());
        if idx == 0 {
            break;
        }
        idx -= 1;
    }
    block.reverse();
    if block.is_empty() { None } else { Some(block) }
}

struct SpecExprLowerer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    binding_info: &'a HirBindingInfo,
}

impl<'a, 'tcx> SpecExprLowerer<'a, 'tcx> {
    fn lower_syn_spec_expr(
        &self,
        expr: &SynExpr,
        span: Span,
        anchor_span: Span,
        kind: &str,
    ) -> Result<SpecExpr, LoopPrepassError> {
        match expr {
            SynExpr::Lit(lit) => match &lit.lit {
                SynLit::Bool(value) => Ok(SpecExpr::Bool(value.value)),
                SynLit::Int(value) => {
                    let value = value.base10_parse::<i64>().map_err(|_| LoopPrepassError {
                        span,
                        basic_block: None,
                        statement_index: None,
                        message: format!("integer literal in //@ {} is too large", kind),
                    })?;
                    Ok(SpecExpr::Int(value))
                }
                _ => Err(self.unsupported_syn_spec_expr(
                    span,
                    kind,
                    "unsupported literal in //@ {kind} predicate",
                )),
            },
            SynExpr::Path(path) => {
                let Some(ident) = path.path.get_ident() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "unsupported path in //@ {kind} predicate",
                    ));
                };
                if ident == "result" {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "`result` is only supported in //@ ens predicates",
                    ));
                }
                let name = Symbol::intern(&ident.to_string());
                let Some(hir_id) = self.resolve_binding_hir_id(name, anchor_span) else {
                    return Err(LoopPrepassError {
                        span,
                        basic_block: None,
                        statement_index: None,
                        message: format!("unresolved binding `{ident}` in //@ {}", kind),
                    });
                };
                Ok(SpecExpr::Var { hir_id, name })
            }
            SynExpr::Call(expr) => {
                let SynExpr::Path(path) = expr.func.as_ref() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "unsupported call in //@ {kind} predicate",
                    ));
                };
                let Some(ident) = path.path.get_ident() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "unsupported call in //@ {kind} predicate",
                    ));
                };
                if ident != "__prophecy" || expr.args.len() != 1 {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "unsupported call in //@ {kind} predicate",
                    ));
                }
                let Some(SynExpr::Path(arg_path)) = expr.args.first() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "unsupported prophecy argument in //@ {kind} predicate",
                    ));
                };
                let Some(arg_ident) = arg_path.path.get_ident() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "unsupported prophecy argument in //@ {kind} predicate",
                    ));
                };
                let name = Symbol::intern(&arg_ident.to_string());
                let Some(hir_id) = self.resolve_binding_hir_id(name, anchor_span) else {
                    return Err(LoopPrepassError {
                        span,
                        basic_block: None,
                        statement_index: None,
                        message: format!("unresolved binding `{arg_ident}` in //@ {}", kind),
                    });
                };
                Ok(SpecExpr::Prophecy { hir_id, name })
            }
            SynExpr::Unary(expr) => {
                let op = match expr.op {
                    SynUnOp::Not(_) => SpecUnaryOp::Not,
                    SynUnOp::Neg(_) => SpecUnaryOp::Neg,
                    _ => {
                        return Err(self.unsupported_syn_spec_expr(
                            span,
                            kind,
                            "unsupported unary operator in //@ {kind} predicate",
                        ));
                    }
                };
                Ok(SpecExpr::Unary {
                    op,
                    arg: Box::new(self.lower_syn_spec_expr(&expr.expr, span, anchor_span, kind)?),
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
                            kind,
                            "unsupported binary operator in //@ {kind} predicate",
                        ));
                    }
                };
                Ok(SpecExpr::Binary {
                    op,
                    lhs: Box::new(self.lower_syn_spec_expr(&expr.left, span, anchor_span, kind)?),
                    rhs: Box::new(self.lower_syn_spec_expr(
                        &expr.right,
                        span,
                        anchor_span,
                        kind,
                    )?),
                })
            }
            SynExpr::Paren(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span, kind),
            SynExpr::Group(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span, kind),
            SynExpr::Reference(expr) => {
                self.lower_syn_spec_expr(&expr.expr, span, anchor_span, kind)
            }
            SynExpr::Cast(expr) => self.lower_syn_spec_expr(&expr.expr, span, anchor_span, kind),
            SynExpr::Block(expr) => {
                let Some(syn::Stmt::Expr(inner, None)) = expr.block.stmts.last() else {
                    return Err(self.unsupported_syn_spec_expr(
                        span,
                        kind,
                        "block without a trailing expression is unsupported in //@ {kind}",
                    ));
                };
                self.lower_syn_spec_expr(inner, span, anchor_span, kind)
            }
            SynExpr::MethodCall(_) => Err(self.unsupported_syn_spec_expr(
                span,
                kind,
                "function calls are unsupported in //@ {kind} predicates",
            )),
            _ => Err(self.unsupported_syn_spec_expr(
                span,
                kind,
                "unsupported expression in //@ {kind} predicate",
            )),
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

    fn unsupported_syn_spec_expr(&self, span: Span, kind: &str, message: &str) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: message.replace("{kind}", kind),
        }
    }
}

struct HirLoopContractCollector<'a, 'tcx> {
    lowerer: SpecExprLowerer<'a, 'tcx>,
    contracts: HashMap<HirId, HirLoopContract>,
}

struct HirAssertionCollector<'a, 'tcx> {
    lowerer: SpecExprLowerer<'a, 'tcx>,
    assertions: Vec<HirAssertionContract>,
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
    ) -> Result<(SpecExpr, String), LoopPrepassError> {
        let loop_source = self
            .lowerer
            .tcx
            .sess
            .source_map()
            .span_to_snippet(loop_expr.span)
            .map_err(|_| self.missing_invariant_error(loop_expr, body))?;
        let body_source = self
            .lowerer
            .tcx
            .sess
            .source_map()
            .span_to_snippet(body.span)
            .map_err(|_| self.missing_invariant_error(loop_expr, body))?;
        let Some(body_index) = loop_source.find(&body_source) else {
            return Err(self.missing_invariant_error(loop_expr, body));
        };
        let prefix_source = &loop_source[..body_index];
        let Some((directive_pos, directive_line)) = spec_directive_line(
            prefix_source,
            "//@ inv",
            true,
            false,
            self.missing_invariant_error(loop_expr, body),
            self.multiple_invariant_error(entry_span),
            self.invariant_position_error(entry_span),
        )?
        else {
            return Err(self.missing_invariant_error(loop_expr, body));
        };

        let predicate_text = directive_line
            .strip_prefix("//@ inv")
            .expect("directive line starts with //@ inv")
            .trim();
        let line_start = prefix_source[..directive_pos]
            .rfind('\n')
            .map(|idx| idx + 1)
            .unwrap_or(0);
        let line_end = prefix_source[directive_pos..]
            .find('\n')
            .map(|idx| directive_pos + idx)
            .unwrap_or(prefix_source.len());
        let line_no = self
            .lowerer
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(body.span.lo())
            .line
            .saturating_sub(1);
        let file_name = self
            .lowerer
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(body.span.lo())
            .file
            .name
            .prefer_local()
            .to_string();
        let line_text = &prefix_source[line_start..line_end];
        let lit = syn::parse_str::<LitStr>(predicate_text).map_err(|err| LoopPrepassError {
            span: entry_span,
            basic_block: None,
            statement_index: None,
            message: format!("failed to parse //@ inv predicate: {err}"),
        })?;
        let expr = parse_spec_template("inv", &lit).map_err(|err| LoopPrepassError {
            span: entry_span,
            basic_block: None,
            statement_index: None,
            message: err.to_string(),
        })?;
        let invariant = self
            .lowerer
            .lower_syn_spec_expr(&expr, entry_span, entry_span, "inv")?;
        Ok((invariant, display_line_span(&file_name, line_no, line_text)))
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
                self.lowerer
                    .tcx
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

impl<'a, 'tcx> Visitor<'tcx> for HirAssertionCollector<'a, 'tcx> {
    type NestedFilter = intravisit::nested_filter::None;
    type Result = ControlFlow<LoopPrepassError>;

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) -> Self::Result {
        if let Err(err) = self.collect_block_assertions(block) {
            return ControlFlow::Break(err);
        }
        intravisit::walk_block(self, block)
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

impl<'a, 'tcx> HirAssertionCollector<'a, 'tcx> {
    fn collect_block_assertions(
        &mut self,
        block: &'tcx Block<'tcx>,
    ) -> Result<(), LoopPrepassError> {
        let Ok(block_source) = self
            .lowerer
            .tcx
            .sess
            .source_map()
            .span_to_snippet(block.span)
        else {
            return Ok(());
        };
        let mut cursor = 0;
        for stmt in block.stmts {
            let stmt_source = self
                .lowerer
                .tcx
                .sess
                .source_map()
                .span_to_snippet(stmt.span)
                .map_err(|_| self.missing_assertion_error(stmt.span))?;
            let Some(stmt_offset) = block_source[cursor..].find(&stmt_source) else {
                continue;
            };
            let stmt_start = cursor + stmt_offset;
            let prefix_source = &block_source[cursor..stmt_start];
            if let Some((directive_pos, directive_line)) = spec_directive_line(
                prefix_source,
                "//@ assert",
                false,
                false,
                self.missing_assertion_error(stmt.span),
                self.multiple_assertion_error(stmt.span),
                self.assertion_position_error(stmt.span),
            )? {
                let predicate_text = directive_line
                    .strip_prefix("//@ assert")
                    .expect("directive line starts with //@ assert")
                    .trim();
                let line_start = prefix_source[..directive_pos]
                    .rfind('\n')
                    .map(|idx| idx + 1)
                    .unwrap_or(0);
                let line_end = prefix_source[directive_pos..]
                    .find('\n')
                    .map(|idx| directive_pos + idx)
                    .unwrap_or(prefix_source.len());
                let line_no = self
                    .lowerer
                    .tcx
                    .sess
                    .source_map()
                    .lookup_char_pos(stmt.span.lo())
                    .line
                    .saturating_sub(1);
                let file_name = self
                    .lowerer
                    .tcx
                    .sess
                    .source_map()
                    .lookup_char_pos(stmt.span.lo())
                    .file
                    .name
                    .prefer_local()
                    .to_string();
                let line_text = &prefix_source[line_start..line_end];
                let lit =
                    syn::parse_str::<LitStr>(predicate_text).map_err(|err| LoopPrepassError {
                        span: stmt.span,
                        basic_block: None,
                        statement_index: None,
                        message: format!("failed to parse //@ assert predicate: {err}"),
                    })?;
                let expr = parse_spec_template("assert", &lit).map_err(|err| LoopPrepassError {
                    span: stmt.span,
                    basic_block: None,
                    statement_index: None,
                    message: err.to_string(),
                })?;
                let assertion = self
                    .lowerer
                    .lower_syn_spec_expr(&expr, stmt.span, stmt.span, "assert")?;
                self.assertions.push(HirAssertionContract {
                    stmt_span: stmt.span,
                    assertion,
                    assertion_span: display_line_span(&file_name, line_no, line_text),
                });
            }
            cursor = stmt_start + stmt_source.len();
        }

        let tail_source = &block_source[cursor..];
        if let Some((directive_pos, directive_line)) = spec_directive_line(
            tail_source,
            "//@ assert",
            false,
            true,
            self.missing_assertion_error(block.span),
            self.multiple_assertion_error(block.span),
            self.assertion_position_error(block.span),
        )? {
            let predicate_text = directive_line
                .strip_prefix("//@ assert")
                .expect("directive line starts with //@ assert")
                .trim();
            let line_start = tail_source[..directive_pos]
                .rfind('\n')
                .map(|idx| idx + 1)
                .unwrap_or(0);
            let line_end = tail_source[directive_pos..]
                .find('\n')
                .map(|idx| directive_pos + idx)
                .unwrap_or(tail_source.len());
            let line_no = self
                .lowerer
                .tcx
                .sess
                .source_map()
                .lookup_char_pos(block.span.hi())
                .line
                .saturating_sub(1);
            let file_name = self
                .lowerer
                .tcx
                .sess
                .source_map()
                .lookup_char_pos(block.span.lo())
                .file
                .name
                .prefer_local()
                .to_string();
            let line_text = &tail_source[line_start..line_end];
            let lit = syn::parse_str::<LitStr>(predicate_text).map_err(|err| LoopPrepassError {
                span: block.span,
                basic_block: None,
                statement_index: None,
                message: format!("failed to parse //@ assert predicate: {err}"),
            })?;
            let expr = parse_spec_template("assert", &lit).map_err(|err| LoopPrepassError {
                span: block.span,
                basic_block: None,
                statement_index: None,
                message: err.to_string(),
            })?;
            let anchor_span = block.span.shrink_to_hi();
            let assertion =
                self.lowerer
                    .lower_syn_spec_expr(&expr, block.span, anchor_span, "assert")?;
            self.assertions.push(HirAssertionContract {
                stmt_span: anchor_span,
                assertion,
                assertion_span: display_line_span(&file_name, line_no, line_text),
            });
        }
        Ok(())
    }

    fn missing_assertion_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "assertion directive must be attached to a statement".to_owned(),
        }
    }

    fn multiple_assertion_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "statement may contain exactly one //@ assert before it".to_owned(),
        }
    }

    fn assertion_position_error(&self, span: Span) -> LoopPrepassError {
        LoopPrepassError {
            span,
            basic_block: None,
            statement_index: None,
            message: "//@ assert must be placed immediately before the statement".to_owned(),
        }
    }
}

fn spec_directive_line<'a>(
    prefix_source: &'a str,
    directive: &str,
    allow_leading_code: bool,
    allow_terminal: bool,
    missing_error: LoopPrepassError,
    multiple_error: LoopPrepassError,
    position_error: LoopPrepassError,
) -> Result<Option<(usize, &'a str)>, LoopPrepassError> {
    let directive_count = prefix_source.matches(directive).count();
    if directive_count == 0 {
        return Ok(None);
    }
    if directive_count > 1 {
        return Err(multiple_error);
    }

    let Some(directive_pos) = prefix_source.rfind(directive) else {
        return Err(missing_error);
    };
    if !allow_leading_code {
        let line_start = prefix_source[..directive_pos]
            .rfind('\n')
            .map(|idx| idx + 1)
            .unwrap_or(0);
        if !prefix_source[line_start..directive_pos].trim().is_empty() {
            return Err(position_error);
        }
    }

    let line_end = prefix_source[directive_pos..]
        .find('\n')
        .map(|idx| directive_pos + idx)
        .unwrap_or(prefix_source.len());
    let directive_line = prefix_source[directive_pos..line_end].trim_end_matches(['\r', ' ', '\t']);
    let after_line = &prefix_source[line_end..];
    if after_line.is_empty() {
        return if allow_terminal {
            Ok(Some((directive_pos, directive_line)))
        } else {
            Err(position_error)
        };
    }
    if allow_terminal && after_line.chars().all(|c| c.is_whitespace() || c == '}') {
        return Ok(Some((directive_pos, directive_line)));
    }
    let Some(after_newline) = after_line.strip_prefix('\n') else {
        return Err(position_error);
    };
    if after_newline.contains('\n') {
        return Err(position_error);
    }
    if !after_newline
        .chars()
        .all(|c| matches!(c, ' ' | '\t' | '\r'))
    {
        return Err(position_error);
    }

    Ok(Some((directive_pos, directive_line)))
}

pub(crate) fn parse_spec_template(kind: &str, lit: &LitStr) -> syn::Result<SynExpr> {
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
                        format!("unclosed `{{` in //@ {} template", kind),
                    ));
                }
                let inner = inner.trim();
                if inner.is_empty() {
                    return Err(syn::Error::new(
                        lit.span(),
                        format!("empty interpolation in //@ {} template", kind),
                    ));
                }
                if let Some(rest) = inner.strip_prefix("^:") {
                    let ident = rest.trim();
                    if ident.is_empty()
                        || !ident
                            .chars()
                            .next()
                            .is_some_and(|ch| ch.is_alphabetic() || ch == '_')
                        || !ident.chars().all(|ch| ch.is_alphanumeric() || ch == '_')
                    {
                        return Err(syn::Error::new(
                            lit.span(),
                            format!("invalid prophecy interpolation in //@ {} template", kind),
                        ));
                    }
                    output.push_str("(__prophecy(");
                    output.push_str(ident);
                    output.push_str("))");
                    continue;
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
                        format!("unmatched `}}` in //@ {} template", kind),
                    ));
                }
            }
            _ => output.push(ch),
        }
    }

    syn::parse_str::<SynExpr>(&output).map_err(|err| {
        syn::Error::new(
            lit.span(),
            format!("failed to parse //@ {} predicate: {err}", kind),
        )
    })
}

fn verify_marker_in_source(source: &str, line: usize) -> bool {
    if line <= 1 {
        return false;
    }
    let mut current = line.saturating_sub(2);
    while let Some(text) = source.lines().nth(current) {
        let trimmed = text.trim();
        if trimmed.is_empty() {
            return false;
        }
        if !trimmed.starts_with("//@") {
            return false;
        }
        if trimmed == "//@ verify" {
            return true;
        }
        if current == 0 {
            break;
        }
        current -= 1;
    }
    false
}

fn parse_function_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: Span,
    kind: &str,
    text: &str,
) -> Result<SynExpr, VerificationResult> {
    let lit = syn::parse_str::<LitStr>(text).map_err(|err| {
        function_contract_error(
            tcx,
            def_id,
            span,
            format!("failed to parse //@ {kind} predicate: {err}"),
        )
    })?;
    parse_spec_template(kind, &lit)
        .map_err(|err| function_contract_error(tcx, def_id, span, err.to_string()))
}

fn function_contract_error<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    span: Span,
    message: String,
) -> VerificationResult {
    VerificationResult {
        function: tcx.def_path_str(def_id.to_def_id()),
        status: VerificationStatus::Unsupported,
        span: tcx.sess.source_map().span_to_diagnostic_string(span),
        message,
    }
}

#[cfg(test)]
mod tests {
    use super::{function_contract_lines_before_item, verify_marker_in_source};

    #[test]
    fn detects_verify_marker_on_previous_line() {
        let source = "fn ignored() {}\n//@ verify\nfn marked() {}\n";
        assert!(verify_marker_in_source(source, 3));
    }

    #[test]
    fn ignores_non_adjacent_marker() {
        let source = "//@ verify\n\nfn marked() {}\n";
        assert!(!verify_marker_in_source(source, 3));
    }

    #[test]
    fn collects_function_contract_lines_before_item() {
        let source =
            "\n//@ req \"true\"\n//@ ens \"{result} == 3\"\nfn callee() -> i32 {\n    2\n}\n";
        let lines = function_contract_lines_before_item(source, 4).unwrap();
        assert_eq!(
            lines,
            vec![
                "//@ req \"true\"".to_owned(),
                "//@ ens \"{result} == 3\"".to_owned()
            ]
        );
    }
}
