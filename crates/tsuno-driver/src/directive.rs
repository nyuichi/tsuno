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
    pub attach: DirectiveAttach,
    pub expr: spec::Expr,
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
            directives.sort_by_key(|directive| directive.span.lo());
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
        } else {
            continue;
        };
        let expr = parse_directive_expr(kind, rest.trim(), item_span)?;
        directives.push(FunctionDirective {
            kind,
            span: item_span,
            span_text: display_line_span(&file_name, line_no, raw_line),
            attach: DirectiveAttach::Function,
            expr,
        });
    }
    Ok(directives)
}

fn parse_directive_expr(
    kind: DirectiveKind,
    text: &str,
    span: Span,
) -> Result<spec::Expr, DirectiveError> {
    if kind == DirectiveKind::LemmaCall {
        return spec::parse_templated_expr("lemma call", text.trim_end_matches(';').trim())
            .map_err(|err| DirectiveError {
                span,
                message: err.to_string().replace("spec expression", "//@ lemma call"),
            });
    }
    spec::parse_expr(kind.keyword(), text).map_err(|err| DirectiveError {
        span,
        message: render_parse_error(kind, err),
    })
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
        let expr = parse_directive_expr(DirectiveKind::Inv, predicate_text, entry_span)?;
        self.directives.push(FunctionDirective {
            kind: DirectiveKind::Inv,
            span: entry_span,
            span_text,
            attach: DirectiveAttach::Loop {
                loop_expr_id: loop_expr.hir_id,
                loop_span: loop_expr.span,
                body_span: loop_body.span,
                entry_span,
            },
            expr,
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
            let stmt_source = self
                .tcx
                .sess
                .source_map()
                .span_to_snippet(stmt.span)
                .map_err(|_| {
                    self.invalid_statement_directive_error(stmt.span, DirectiveKind::Assert)
                })?;
            let Some(stmt_offset) = block_source[cursor..].find(&stmt_source) else {
                continue;
            };
            let stmt_start = cursor + stmt_offset;
            let prefix_source = &block_source[cursor..stmt_start];
            let line_anchor = self
                .tcx
                .sess
                .source_map()
                .lookup_char_pos(stmt.span.lo())
                .line;
            let mut directives = self.collect_statement_directives(
                prefix_source,
                stmt.span,
                line_anchor,
                &file_name,
                false,
            )?;
            self.directives.append(&mut directives);
            cursor = stmt_start + stmt_source.len();
        }

        let tail_source = &block_source[cursor..];
        let line_anchor = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(block.span.hi())
            .line;
        let anchor_span = block.span.shrink_to_hi();
        let mut directives = self.collect_statement_directives(
            tail_source,
            anchor_span,
            line_anchor,
            &file_name,
            true,
        )?;
        self.directives.append(&mut directives);
        Ok(())
    }

    fn collect_statement_directives(
        &self,
        source: &str,
        anchor_span: Span,
        line_anchor: usize,
        file_name: &str,
        allow_terminal: bool,
    ) -> Result<Vec<FunctionDirective>, DirectiveError> {
        let mut found = Vec::new();
        for kind in [DirectiveKind::Assert, DirectiveKind::Assume] {
            let directive = format!("//@ {}", kind.keyword());
            if let Some((directive_pos, directive_line)) = spec_directive_line(
                source,
                &directive,
                false,
                allow_terminal,
                self.multiple_statement_directive_error(anchor_span, kind),
                self.statement_directive_position_error(anchor_span, kind),
            )? {
                let predicate_text = directive_line
                    .strip_prefix(&directive)
                    .expect("directive line starts with keyword")
                    .trim();
                let expr = parse_directive_expr(kind, predicate_text, anchor_span)?;
                let line_no = directive_line_number(line_anchor, source, directive_pos);
                let span_text = display_line_span(
                    file_name,
                    line_no,
                    directive_line_text(source, directive_pos),
                );
                found.push((
                    directive_pos,
                    FunctionDirective {
                        kind,
                        span: anchor_span,
                        span_text,
                        attach: DirectiveAttach::Statement { anchor_span },
                        expr,
                    },
                ));
            }
        }
        if found.is_empty()
            && let Some((directive_pos, directive_line)) = generic_ghost_statement_line(
                source,
                allow_terminal,
                self.multiple_statement_directive_error(anchor_span, DirectiveKind::LemmaCall),
                self.statement_directive_position_error(anchor_span, DirectiveKind::LemmaCall),
            )?
        {
            let predicate_text = directive_line
                .strip_prefix("//@")
                .expect("directive line starts with //@")
                .trim();
            let expr = parse_directive_expr(DirectiveKind::LemmaCall, predicate_text, anchor_span)?;
            let line_no = directive_line_number(line_anchor, source, directive_pos);
            let span_text = display_line_span(
                file_name,
                line_no,
                directive_line_text(source, directive_pos),
            );
            found.push((
                directive_pos,
                FunctionDirective {
                    kind: DirectiveKind::LemmaCall,
                    span: anchor_span,
                    span_text,
                    attach: DirectiveAttach::Statement { anchor_span },
                    expr,
                },
            ));
        }
        found.sort_by_key(|(directive_pos, _)| *directive_pos);
        Ok(found.into_iter().map(|(_, directive)| directive).collect())
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
                "loop body starting at {} requires exactly one //@ inv \"...\" before the body",
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

    fn multiple_statement_directive_error(
        &self,
        span: Span,
        kind: DirectiveKind,
    ) -> DirectiveError {
        DirectiveError {
            span,
            message: match kind {
                DirectiveKind::Assert => {
                    "statement may contain exactly one //@ assert before it".to_owned()
                }
                DirectiveKind::Assume => {
                    "statement may contain exactly one //@ assume before it".to_owned()
                }
                DirectiveKind::LemmaCall => {
                    "statement may contain exactly one ghost statement before it".to_owned()
                }
                _ => "statement may contain exactly one directive before it".to_owned(),
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

fn generic_ghost_statement_line<'a>(
    source: &'a str,
    allow_terminal: bool,
    multiple_error: DirectiveError,
    position_error: DirectiveError,
) -> Result<Option<(usize, &'a str)>, DirectiveError> {
    let mut candidate = None;
    for (directive_pos, _) in source.match_indices("//@") {
        let line_start = source[..directive_pos]
            .rfind('\n')
            .map(|idx| idx + 1)
            .unwrap_or(0);
        let line_end = source[directive_pos..]
            .find('\n')
            .map(|idx| directive_pos + idx)
            .unwrap_or(source.len());
        let directive_line = source[directive_pos..line_end].trim_end_matches(['\r', ' ', '\t']);
        let predicate_text = directive_line
            .strip_prefix("//@")
            .expect("directive line starts with //@")
            .trim();
        if matches_reserved_statement_directive(predicate_text) {
            continue;
        }
        if candidate
            .replace((directive_pos, directive_line, line_start, line_end))
            .is_some()
        {
            return Err(multiple_error);
        }
    }
    let Some((directive_pos, directive_line, line_start, line_end)) = candidate else {
        return Ok(None);
    };
    if !source[line_start..directive_pos].trim().is_empty() {
        return Err(position_error);
    }
    let after_line = &source[line_end..];
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
}

#[cfg(test)]
mod tests {
    use super::{function_contract_lines_before_body, function_contract_lines_before_item};

    #[test]
    fn collects_function_contract_lines_before_body() {
        let source =
            "fn callee() -> i32\n//@ req \"true\"\n//@ ens \"{result} == 3\"\n{\n    2\n}\n";
        let lines = function_contract_lines_before_body(source, 4).unwrap();
        assert_eq!(
            lines,
            vec![
                "//@ req \"true\"".to_owned(),
                "//@ ens \"{result} == 3\"".to_owned()
            ]
        );
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
