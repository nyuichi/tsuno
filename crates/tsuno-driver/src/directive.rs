use std::ops::ControlFlow;

use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Block, Expr, ExprKind, HirId, LoopSource, MatchSource, Stmt, StmtKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;

use crate::spec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveKind {
    Req,
    Ens,
    Let,
    Inv,
    Assert,
    Assume,
    LemmaCall,
}

impl DirectiveKind {
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Req => "req",
            Self::Ens => "ens",
            Self::Let => "let",
            Self::Inv => "inv",
            Self::Assert => "assert",
            Self::Assume => "assume",
            Self::LemmaCall => "lemma_call",
        }
    }
}

#[derive(Debug, Clone)]
pub enum DirectiveAttach {
    Function,
    Statement {
        anchor_span: Span,
    },
    Loop {
        loop_expr_id: HirId,
        loop_span: Span,
        body_span: Span,
        entry_span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct FunctionDirective {
    pub kind: DirectiveKind,
    pub span: Span,
    pub span_text: String,
    pub line_no: usize,
    pub attach: DirectiveAttach,
    pub payload: DirectivePayload,
    pub scope_span: Option<Span>,
}

#[derive(Debug, Clone)]
pub enum DirectivePayload {
    Predicate(spec::Expr),
    Let { name: String, value: spec::Expr },
    LemmaCall(spec::Expr),
}

impl FunctionDirective {
    pub fn expr(&self) -> &spec::Expr {
        match &self.payload {
            DirectivePayload::Predicate(expr) | DirectivePayload::LemmaCall(expr) => expr,
            DirectivePayload::Let { value, .. } => value,
        }
    }

    pub fn let_binding(&self) -> Option<(&str, &spec::Expr)> {
        match &self.payload {
            DirectivePayload::Let { name, value } => Some((name, value)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CollectedFunctionDirectives {
    pub directives: Vec<FunctionDirective>,
}

#[derive(Debug, Clone)]
pub struct DirectiveError {
    pub span: Span,
    pub message: String,
}

pub fn collect_function_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    item_span: Span,
) -> Result<CollectedFunctionDirectives, DirectiveError> {
    let body = tcx.hir_body_owned_by(def_id);
    let mut directives = collect_contract_directives(tcx, def_id, item_span, body.value.span)?;
    let mut collector = FunctionDirectiveCollector {
        tcx,
        directives: Vec::new(),
    };
    match intravisit::walk_body(&mut collector, body) {
        ControlFlow::Continue(()) => {
            directives.extend(collector.directives);
            directives.sort_by_key(|directive| directive.line_no);
            Ok(CollectedFunctionDirectives { directives })
        }
        ControlFlow::Break(err) => Err(err),
    }
}

fn collect_contract_directives<'tcx>(
    tcx: TyCtxt<'tcx>,
    _def_id: LocalDefId,
    item_span: Span,
    body_span: Span,
) -> Result<Vec<FunctionDirective>, DirectiveError> {
    let loc = tcx.sess.source_map().lookup_char_pos(item_span.lo());
    let Some(source) = loc.file.src.as_deref() else {
        return Ok(Vec::new());
    };
    if let Some(lines) = function_contract_lines_before_item(source, loc.line)
        && lines
            .iter()
            .any(|line| line.starts_with("//@ req") || line.starts_with("//@ ens"))
    {
        return Err(DirectiveError {
            span: item_span,
            message:
                "function contract directives must be placed immediately before the function body"
                    .to_owned(),
        });
    }

    let body_line = tcx.sess.source_map().lookup_char_pos(body_span.lo()).line;
    let Some(lines) = function_contract_lines_before_body(source, body_line) else {
        return Ok(Vec::new());
    };

    let file_name = loc.file.name.prefer_local().to_string();
    let block_start_line = body_line - lines.len();
    let mut directives = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        let line_no = block_start_line + index;
        let raw_line = source.lines().nth(line_no - 1).unwrap_or(line).trim_end();
        let (kind, rest) = if let Some(rest) = line.strip_prefix("//@ req") {
            (DirectiveKind::Req, rest)
        } else if let Some(rest) = line.strip_prefix("//@ ens") {
            (DirectiveKind::Ens, rest)
        } else if let Some(rest) = line.strip_prefix("//@ let") {
            (DirectiveKind::Let, rest)
        } else {
            continue;
        };
        let payload = parse_directive_payload(kind, rest.trim(), item_span)?;
        directives.push(FunctionDirective {
            kind,
            span: item_span,
            span_text: display_line_span(&file_name, line_no, raw_line),
            line_no,
            attach: DirectiveAttach::Function,
            payload,
            scope_span: None,
        });
    }
    Ok(directives)
}

fn parse_directive_payload(
    kind: DirectiveKind,
    text: &str,
    span: Span,
) -> Result<DirectivePayload, DirectiveError> {
    if kind == DirectiveKind::LemmaCall {
        return spec::parse_statement_expr("lemma call", text.trim())
            .map_err(|err| DirectiveError {
                span,
                message: err.to_string().replace("spec expression", "//@ lemma call"),
            })
            .map(DirectivePayload::LemmaCall);
    }
    if kind == DirectiveKind::Let {
        return parse_let_directive(text, span);
    }
    let parsed = match kind {
        DirectiveKind::Assert | DirectiveKind::Assume => {
            spec::parse_statement_expr(kind.keyword(), text)
        }
        _ => spec::parse_source_expr(kind.keyword(), text),
    };
    parsed
        .map_err(|err| DirectiveError {
            span,
            message: render_parse_error(kind, err),
        })
        .map(DirectivePayload::Predicate)
}

fn parse_let_directive(text: &str, span: Span) -> Result<DirectivePayload, DirectiveError> {
    let Some(text) = text.strip_suffix(';') else {
        return Err(DirectiveError {
            span,
            message: "//@ let directive must end with `;`".to_owned(),
        });
    };
    let Some((name, value)) = text.split_once('=') else {
        return Err(DirectiveError {
            span,
            message: "//@ let directive must have the form `//@ let name = expr;`".to_owned(),
        });
    };
    let name = name.trim();
    if !is_ident(name) {
        return Err(DirectiveError {
            span,
            message: "//@ let directive must bind an identifier".to_owned(),
        });
    }
    let value = spec::parse_source_expr("let", value.trim()).map_err(|err| DirectiveError {
        span,
        message: render_parse_error(DirectiveKind::Let, err),
    })?;
    Ok(DirectivePayload::Let {
        name: name.to_owned(),
        value,
    })
}

fn is_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn render_parse_error(kind: DirectiveKind, err: spec::ParseError) -> String {
    err.to_string().replace(
        "spec expression",
        &format!("//@ {} predicate", kind.keyword()),
    )
}

fn display_line_span(file_name: &str, line_no: usize, line_text: &str) -> String {
    let start_col = line_text.chars().take_while(|c| c.is_whitespace()).count() + 1;
    let end_col = start_col + line_text.trim_end().chars().count();
    format!("{file_name}:{line_no}:{start_col}: {line_no}:{end_col}")
}

pub(crate) fn function_contract_lines_before_item(
    source: &str,
    item_line: usize,
) -> Option<Vec<String>> {
    function_contract_lines_before_line(source, item_line)
}

pub(crate) fn function_contract_lines_before_body(
    source: &str,
    body_line: usize,
) -> Option<Vec<String>> {
    function_contract_lines_before_line(source, body_line)
}

fn function_contract_lines_before_line(source: &str, line_no: usize) -> Option<Vec<String>> {
    if line_no <= 1 {
        return None;
    }

    let lines: Vec<_> = source.lines().collect();
    let mut idx = line_no.saturating_sub(2);
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

struct FunctionDirectiveCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    directives: Vec<FunctionDirective>,
}

impl<'a> FunctionDirectiveCollector<'a> {
    fn collect_loop_directive(
        &mut self,
        loop_expr: &'a Expr<'a>,
        body: &'a Block<'a>,
        source: LoopSource,
    ) -> Result<(), DirectiveError> {
        let loop_body = self.loop_body_block(loop_expr, body, source)?;
        let entry_span = body_entry_span(loop_body);
        let loop_source = self
            .tcx
            .sess
            .source_map()
            .span_to_snippet(loop_expr.span)
            .map_err(|_| self.missing_invariant_error(loop_expr, loop_body))?;
        let body_source = self
            .tcx
            .sess
            .source_map()
            .span_to_snippet(loop_body.span)
            .map_err(|_| self.missing_invariant_error(loop_expr, loop_body))?;
        let Some(body_index) = loop_source.find(&body_source) else {
            return Err(self.missing_invariant_error(loop_expr, loop_body));
        };
        let prefix_source = &loop_source[..body_index];
        let Some((directive_pos, directive_line)) = spec_directive_line(
            prefix_source,
            "//@ inv",
            true,
            false,
            self.multiple_invariant_error(entry_span),
            self.invariant_position_error(entry_span),
        )?
        else {
            return Err(self.missing_invariant_error(loop_expr, loop_body));
        };

        let predicate_text = directive_line
            .strip_prefix("//@ inv")
            .expect("directive line starts with //@ inv")
            .trim();
        let file_name = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(loop_body.span.lo())
            .file
            .name
            .prefer_local()
            .to_string();
        let line_no = directive_line_number(
            self.tcx
                .sess
                .source_map()
                .lookup_char_pos(loop_body.span.lo())
                .line,
            prefix_source,
            directive_pos,
        );
        let span_text = display_line_span(
            &file_name,
            line_no,
            directive_line_text(prefix_source, directive_pos),
        );
        let payload = parse_directive_payload(DirectiveKind::Inv, predicate_text, entry_span)?;
        self.directives.push(FunctionDirective {
            kind: DirectiveKind::Inv,
            span: entry_span,
            span_text,
            line_no,
            attach: DirectiveAttach::Loop {
                loop_expr_id: loop_expr.hir_id,
                loop_span: loop_expr.span,
                body_span: loop_body.span,
                entry_span,
            },
            payload,
            scope_span: None,
        });
        Ok(())
    }

    fn collect_block_directives(&mut self, block: &'a Block<'a>) -> Result<(), DirectiveError> {
        let Ok(block_source) = self.tcx.sess.source_map().span_to_snippet(block.span) else {
            return Ok(());
        };
        let file_name = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(block.span.lo())
            .file
            .name
            .prefer_local()
            .to_string();
        let mut cursor = 0;
        for stmt in block.stmts {
            cursor = self.collect_anchor_directives(
                &block_source,
                block.span,
                cursor,
                stmt.span,
                &file_name,
                false,
            )?;
        }

        if let Some(expr) = block.expr {
            cursor = self.collect_anchor_directives(
                &block_source,
                block.span,
                cursor,
                expr.span,
                &file_name,
                false,
            )?;
        }

        let tail_source = &block_source[cursor..];
        let line_anchor = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(block.span.hi())
            .line;
        let anchor_span = block.span.shrink_to_hi();
        let mut directives = self.collect_anchor_directive_lines(
            tail_source,
            anchor_span,
            line_anchor,
            &file_name,
            true,
            Some(block.span),
        )?;
        self.directives.append(&mut directives);
        Ok(())
    }

    fn collect_anchor_directives(
        &mut self,
        block_source: &str,
        block_span: Span,
        cursor: usize,
        anchor_span: Span,
        file_name: &str,
        allow_terminal: bool,
    ) -> Result<usize, DirectiveError> {
        let anchor_start = anchor_span
            .lo()
            .0
            .checked_sub(block_span.lo().0)
            .map(|offset| offset as usize)
            .filter(|offset| *offset <= block_source.len())
            .ok_or_else(|| {
                self.invalid_statement_directive_error(anchor_span, DirectiveKind::Assert)
            })?;
        let anchor_end = anchor_span
            .hi()
            .0
            .checked_sub(block_span.lo().0)
            .map(|offset| offset as usize)
            .filter(|offset| *offset <= block_source.len())
            .ok_or_else(|| {
                self.invalid_statement_directive_error(anchor_span, DirectiveKind::Assert)
            })?;
        if anchor_start < cursor || anchor_end < anchor_start {
            return Ok(cursor);
        }
        let prefix_source = &block_source[cursor..anchor_start];
        let line_anchor = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(anchor_span.lo())
            .line;
        let mut directives = self.collect_anchor_directive_lines(
            prefix_source,
            anchor_span,
            line_anchor,
            file_name,
            allow_terminal,
            Some(block_span),
        )?;
        self.directives.append(&mut directives);
        Ok(anchor_end)
    }

    fn collect_anchor_directive_lines(
        &self,
        source: &str,
        anchor_span: Span,
        line_anchor: usize,
        file_name: &str,
        allow_terminal: bool,
        scope_span: Option<Span>,
    ) -> Result<Vec<FunctionDirective>, DirectiveError> {
        let body = if allow_terminal {
            trim_terminal_anchor_suffix(source)
        } else {
            source.trim_end_matches(char::is_whitespace)
        };
        let Some(first_directive) = body.find("//@") else {
            return Ok(Vec::new());
        };
        let body = &body[first_directive..];

        let mut found = Vec::new();
        for (directive_pos, directive_line) in directive_lines(
            body,
            self.statement_directive_position_error(anchor_span, DirectiveKind::LemmaCall),
        )? {
            let directive_pos = first_directive + directive_pos;
            let predicate_text = directive_line
                .strip_prefix("//@")
                .expect("directive line starts with //@")
                .trim();
            if matches_reserved_statement_directive(predicate_text)
                && !matches!(
                    classify_statement_directive(predicate_text),
                    Some(DirectiveKind::Assert | DirectiveKind::Assume | DirectiveKind::Let)
                )
            {
                return Err(
                    self.statement_directive_position_error(anchor_span, DirectiveKind::LemmaCall)
                );
            }
            let kind =
                classify_statement_directive(predicate_text).unwrap_or(DirectiveKind::LemmaCall);
            let expr_text = match kind {
                DirectiveKind::Assert => predicate_text
                    .strip_prefix("assert")
                    .expect("assert directive")
                    .trim(),
                DirectiveKind::Assume => predicate_text
                    .strip_prefix("assume")
                    .expect("assume directive")
                    .trim(),
                DirectiveKind::Let => predicate_text
                    .strip_prefix("let")
                    .expect("let directive")
                    .trim(),
                DirectiveKind::LemmaCall => predicate_text,
                _ => unreachable!("unexpected statement directive kind"),
            };
            let payload = parse_directive_payload(kind, expr_text, anchor_span)?;
            let line_no = directive_line_number(line_anchor, source, directive_pos);
            let span_text = display_line_span(file_name, line_no, directive_line);
            found.push(FunctionDirective {
                kind,
                span: anchor_span,
                span_text,
                line_no,
                attach: DirectiveAttach::Statement { anchor_span },
                payload,
                scope_span,
            });
        }
        Ok(found)
    }

    fn loop_body_block(
        &self,
        loop_expr: &'a Expr<'a>,
        body: &'a Block<'a>,
        source: LoopSource,
    ) -> Result<&'a Block<'a>, DirectiveError> {
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

    fn first_loop_control_expr(&self, body: &'a Block<'a>) -> Option<&'a Expr<'a>> {
        if let Some(expr) = body.expr {
            return Some(expr);
        }
        body.stmts.iter().find_map(stmt_expr)
    }

    fn missing_invariant_error(
        &self,
        loop_expr: &'a Expr<'a>,
        body: &'a Block<'a>,
    ) -> DirectiveError {
        DirectiveError {
            span: loop_expr.span,
            message: format!(
                "loop body starting at {} requires exactly one //@ inv <expr> before the body",
                self.tcx
                    .sess
                    .source_map()
                    .span_to_diagnostic_string(body.span)
            ),
        }
    }

    fn multiple_invariant_error(&self, span: Span) -> DirectiveError {
        DirectiveError {
            span,
            message: "loop header may contain exactly one //@ inv before the body".to_owned(),
        }
    }

    fn invariant_position_error(&self, span: Span) -> DirectiveError {
        DirectiveError {
            span,
            message: "//@ inv must be placed immediately before the loop body".to_owned(),
        }
    }

    fn unsupported_loop_shape_error(&self, span: Span) -> DirectiveError {
        DirectiveError {
            span,
            message: "unsupported loop desugaring shape for //@ inv".to_owned(),
        }
    }

    fn invalid_statement_directive_error(&self, span: Span, kind: DirectiveKind) -> DirectiveError {
        DirectiveError {
            span,
            message: match kind {
                DirectiveKind::Assert => {
                    "assertion directive must be attached to a statement".to_owned()
                }
                DirectiveKind::Assume => {
                    "assumption directive must be attached to a statement".to_owned()
                }
                DirectiveKind::LemmaCall => {
                    "lemma call directive must be attached to a statement".to_owned()
                }
                _ => "directive must be attached to a statement".to_owned(),
            },
        }
    }

    fn statement_directive_position_error(
        &self,
        span: Span,
        kind: DirectiveKind,
    ) -> DirectiveError {
        DirectiveError {
            span,
            message: match kind {
                DirectiveKind::Assert => {
                    "//@ assert must be placed immediately before the statement".to_owned()
                }
                DirectiveKind::Assume => {
                    "//@ assume must be placed immediately before the statement".to_owned()
                }
                DirectiveKind::LemmaCall => {
                    "ghost statement must be placed immediately before the statement".to_owned()
                }
                _ => "directive must be placed immediately before the statement".to_owned(),
            },
        }
    }
}

impl<'tcx> Visitor<'tcx> for FunctionDirectiveCollector<'tcx> {
    type NestedFilter = intravisit::nested_filter::None;
    type Result = ControlFlow<DirectiveError>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Self::Result {
        if let ExprKind::Loop(body, _, source, _) = expr.kind
            && let Err(err) = self.collect_loop_directive(expr, body, source)
        {
            return ControlFlow::Break(err);
        }
        intravisit::walk_expr(self, expr)
    }

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) -> Self::Result {
        if let Err(err) = self.collect_block_directives(block) {
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

fn directive_line_number(anchor_line: usize, source: &str, directive_pos: usize) -> usize {
    anchor_line.saturating_sub(source[directive_pos..].matches('\n').count())
}

fn directive_line_text(source: &str, directive_pos: usize) -> &str {
    let line_start = source[..directive_pos]
        .rfind('\n')
        .map(|idx| idx + 1)
        .unwrap_or(0);
    let line_end = source[directive_pos..]
        .find('\n')
        .map(|idx| directive_pos + idx)
        .unwrap_or(source.len());
    &source[line_start..line_end]
}

fn trim_terminal_anchor_suffix(source: &str) -> &str {
    source.trim_end_matches(|c: char| c.is_whitespace() || c == '}')
}

fn directive_lines(
    source: &str,
    position_error: DirectiveError,
) -> Result<Vec<(usize, &str)>, DirectiveError> {
    let mut directives = Vec::new();
    let mut offset = 0;
    for line in source.split_inclusive('\n') {
        let line_end = line.trim_end_matches(['\n', '\r']);
        let trimmed = line_end.trim();
        if trimmed.is_empty() {
            offset += line.len();
            continue;
        }
        let Some(directive_col) = line_end.find("//@") else {
            return Err(position_error.clone());
        };
        if !line_end[..directive_col].trim().is_empty() {
            return Err(position_error.clone());
        }
        directives.push((
            offset + directive_col,
            line_end[directive_col..].trim_end_matches([' ', '\t']),
        ));
        offset += line.len();
    }
    Ok(directives)
}

fn classify_statement_directive(text: &str) -> Option<DirectiveKind> {
    if text.starts_with("assert") {
        Some(DirectiveKind::Assert)
    } else if text.starts_with("assume") {
        Some(DirectiveKind::Assume)
    } else if text.starts_with("let") {
        Some(DirectiveKind::Let)
    } else {
        None
    }
}

fn spec_directive_line<'a>(
    prefix_source: &'a str,
    directive: &str,
    allow_leading_code: bool,
    allow_terminal: bool,
    multiple_error: DirectiveError,
    position_error: DirectiveError,
) -> Result<Option<(usize, &'a str)>, DirectiveError> {
    let directive_count = prefix_source.matches(directive).count();
    if directive_count == 0 {
        return Ok(None);
    }
    if directive_count > 1 {
        return Err(multiple_error);
    }

    let Some(directive_pos) = prefix_source.rfind(directive) else {
        return Ok(None);
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

fn matches_reserved_statement_directive(text: &str) -> bool {
    text.starts_with("assert")
        || text.starts_with("assume")
        || text.starts_with("inv")
        || text.starts_with("req")
        || text.starts_with("ens")
        || text.starts_with("let")
}

#[cfg(test)]
mod tests {
    use super::{function_contract_lines_before_body, function_contract_lines_before_item};

    #[test]
    fn collects_function_contract_lines_before_body() {
        let source = "fn callee() -> i32\n//@ req true\n//@ ens {result} == 3\n{\n    2\n}\n";
        let lines = function_contract_lines_before_body(source, 4).unwrap();
        assert_eq!(
            lines,
            vec![
                "//@ req true".to_owned(),
                "//@ ens {result} == 3".to_owned()
            ]
        );
    }

    #[test]
    fn collects_function_contract_lines_before_item() {
        let source = "\n//@ req true\n//@ ens {result} == 3\nfn callee() -> i32 {\n    2\n}\n";
        let lines = function_contract_lines_before_item(source, 4).unwrap();
        assert_eq!(
            lines,
            vec![
                "//@ req true".to_owned(),
                "//@ ens {result} == 3".to_owned()
            ]
        );
    }
}
