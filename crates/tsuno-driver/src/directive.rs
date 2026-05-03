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
    RawAssert,
    RawReq,
    RawEns,
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
            Self::RawAssert => "raw assert",
            Self::RawReq => "raw req",
            Self::RawEns => "raw ens",
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
    RawAssert(RawAssertion),
    LemmaCall(spec::Expr),
}

impl FunctionDirective {
    pub fn expr(&self) -> &spec::Expr {
        match &self.payload {
            DirectivePayload::Predicate(expr) | DirectivePayload::LemmaCall(expr) => expr,
            DirectivePayload::Let { value, .. } => value,
            DirectivePayload::RawAssert(_) => {
                panic!("raw assertion directive has no single expression")
            }
        }
    }

    pub fn raw_assertion(&self) -> Option<&RawAssertion> {
        match &self.payload {
            DirectivePayload::RawAssert(assertion) => Some(assertion),
            _ => None,
        }
    }

    pub fn let_binding(&self) -> Option<(&str, &spec::Expr)> {
        match &self.payload {
            DirectivePayload::Let { name, value } => Some((name, value)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawAssertion {
    pub pattern: RawPattern,
    pub condition: spec::Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawPattern {
    Star(Box<RawPattern>, Box<RawPattern>),
    PointsTo {
        addr: spec::Expr,
        ty: spec::Expr,
        value: ValuePattern,
    },
    PointsToSugar {
        pointer: String,
        value: ValuePattern,
    },
    DeallocToken {
        base: spec::Expr,
        size: spec::Expr,
        alignment: spec::Expr,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValuePattern {
    Bind(String),
    Expr(spec::Expr),
    SeqLit(Vec<ValuePattern>),
    StructLit {
        name: String,
        fields: Vec<ValuePatternStructField>,
    },
    Call {
        func: String,
        type_args: Vec<spec::SpecTy>,
        args: Vec<ValuePattern>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValuePatternStructField {
    pub name: String,
    pub value: ValuePattern,
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
    if let Some(lines) = function_contract_comment_lines_before_item(source, loc.line)
        && lines
            .iter()
            .any(|line| contract_comment_kind(&line.text).is_some())
    {
        return Err(DirectiveError {
            span: item_span,
            message:
                "function contract directives must be placed immediately before the function body"
                    .to_owned(),
        });
    }

    let body_line = tcx.sess.source_map().lookup_char_pos(body_span.lo()).line;
    let Some(lines) = function_contract_comment_lines_before_body(source, body_line) else {
        return Ok(Vec::new());
    };

    let file_name = loc.file.name.prefer_local().to_string();
    let mut directives = Vec::new();
    for entry in contract_directive_entries(&lines, item_span)? {
        let payload = parse_directive_payload(entry.kind, entry.text.trim(), item_span)?;
        directives.push(FunctionDirective {
            kind: entry.kind,
            span: item_span,
            span_text: display_line_span(&file_name, entry.line_no, &entry.line_text),
            line_no: entry.line_no,
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
    if matches!(
        kind,
        DirectiveKind::RawAssert | DirectiveKind::RawReq | DirectiveKind::RawEns
    ) {
        return parse_raw_assert_directive(text, span);
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

fn parse_raw_assert_directive(text: &str, span: Span) -> Result<DirectivePayload, DirectiveError> {
    parse_raw_assertion(text, span).map(DirectivePayload::RawAssert)
}

pub fn parse_raw_assertion(text: &str, span: Span) -> Result<RawAssertion, DirectiveError> {
    let text = text.trim().strip_suffix(';').unwrap_or(text.trim()).trim();
    let (pattern, condition) = split_raw_assert_where(text);
    let pattern = parse_raw_pattern(pattern, span)?;
    let condition = match condition {
        Some(condition) => parse_raw_assert_expr(condition, span)?,
        None => spec::Expr::Bool(true),
    };
    Ok(RawAssertion { pattern, condition })
}

fn parse_raw_pattern(text: &str, span: Span) -> Result<RawPattern, DirectiveError> {
    let text = strip_enclosing_parens(text.trim());
    if let Some(index) = top_level_star(text) {
        let lhs = parse_raw_pattern(&text[..index], span)?;
        let rhs = parse_raw_pattern(&text[index + 1..], span)?;
        return Ok(RawPattern::Star(Box::new(lhs), Box::new(rhs)));
    }
    if let Some(index) = top_level_points_to_arrow(text) {
        return parse_points_to_sugar(&text[..index], &text[index + "|->".len()..], span);
    }
    if let Some(args) = atom_args(text, "PointsTo") {
        let args = split_top_level_args(args, span)?;
        if args.len() != 3 {
            return Err(DirectiveError {
                span,
                message: "`PointsTo` raw pattern expects three arguments".to_owned(),
            });
        }
        return Ok(RawPattern::PointsTo {
            addr: parse_raw_assert_expr(args[0], span)?,
            ty: parse_raw_assert_expr(args[1], span)?,
            value: parse_value_pattern(args[2], span)?,
        });
    }
    if let Some(args) = atom_args(text, "DeallocToken") {
        let args = split_top_level_args(args, span)?;
        if args.len() != 3 {
            return Err(DirectiveError {
                span,
                message: "`DeallocToken` raw pattern expects three arguments".to_owned(),
            });
        }
        return Ok(RawPattern::DeallocToken {
            base: parse_raw_assert_expr(args[0], span)?,
            size: parse_raw_assert_expr(args[1], span)?,
            alignment: parse_raw_assert_expr(args[2], span)?,
        });
    }
    Err(DirectiveError {
        span,
        message: "raw assertion must be a `PointsTo`, `DeallocToken`, or `*` pattern".to_owned(),
    })
}

fn parse_points_to_sugar(lhs: &str, rhs: &str, span: Span) -> Result<RawPattern, DirectiveError> {
    let lhs = strip_enclosing_parens(lhs.trim());
    let Some(pointer) = lhs.strip_prefix('*').map(str::trim) else {
        return Err(DirectiveError {
            span,
            message: "`|->` raw pattern must have the form `*ptr |-> value`".to_owned(),
        });
    };
    if !is_ident(pointer) {
        return Err(DirectiveError {
            span,
            message: "`|->` raw pattern pointer must be a Rust local name".to_owned(),
        });
    }
    Ok(RawPattern::PointsToSugar {
        pointer: pointer.to_owned(),
        value: parse_value_pattern(rhs, span)?,
    })
}

fn split_raw_assert_where(text: &str) -> (&str, Option<&str>) {
    let mut depth = 0usize;
    for (index, _) in text.match_indices("where") {
        for ch in text[..index].chars() {
            match ch {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' | '}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
        if depth != 0 {
            depth = 0;
            continue;
        }
        let before = text[..index].chars().next_back();
        let after = text[index + "where".len()..].chars().next();
        if before.is_none_or(|ch| ch.is_whitespace()) && after.is_none_or(|ch| ch.is_whitespace()) {
            return (
                text[..index].trim(),
                Some(text[index + "where".len()..].trim()),
            );
        }
        depth = 0;
    }
    (text, None)
}

fn parse_value_pattern(text: &str, span: Span) -> Result<ValuePattern, DirectiveError> {
    let (rewritten, binders) = rewrite_pattern_binders(text, span)?;
    let expr = parse_raw_assert_expr(&rewritten, span)?;
    Ok(expr_to_value_pattern(expr, &binders).0)
}

fn rewrite_pattern_binders(
    text: &str,
    span: Span,
) -> Result<(String, Vec<(String, String)>), DirectiveError> {
    let mut rewritten = String::with_capacity(text.len());
    let mut binders = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((_, ch)) = chars.next() {
        if ch != '?' {
            rewritten.push(ch);
            continue;
        }
        let Some((_, first)) = chars.peek().copied() else {
            return Err(DirectiveError {
                span,
                message: "raw pattern binder must be `?ident`".to_owned(),
            });
        };
        if !(first == '_' || first.is_ascii_alphabetic()) {
            return Err(DirectiveError {
                span,
                message: "raw pattern binder must be `?ident`".to_owned(),
            });
        }
        let mut name = String::new();
        while let Some((_, ch)) = chars.peek().copied() {
            if ch == '_' || ch.is_ascii_alphanumeric() {
                name.push(ch);
                chars.next();
            } else {
                break;
            }
        }
        let placeholder = format!("__tsuno_raw_binder_{}", binders.len());
        rewritten.push_str(&placeholder);
        binders.push((placeholder, name));
    }
    Ok((rewritten, binders))
}

fn expr_to_value_pattern(expr: spec::Expr, binders: &[(String, String)]) -> (ValuePattern, bool) {
    if let spec::Expr::Var(name) = &expr
        && let Some((_, binder)) = binders.iter().find(|(placeholder, _)| placeholder == name)
    {
        return (ValuePattern::Bind(binder.clone()), true);
    }
    match expr {
        spec::Expr::SeqLit(items) => {
            let mut has_pattern = false;
            let items = items
                .into_iter()
                .map(|item| {
                    let (pattern, item_has_pattern) = expr_to_value_pattern(item, binders);
                    has_pattern |= item_has_pattern;
                    pattern
                })
                .collect::<Vec<_>>();
            if has_pattern {
                (ValuePattern::SeqLit(items), true)
            } else {
                (
                    ValuePattern::Expr(spec::Expr::SeqLit(
                        items
                            .into_iter()
                            .map(value_pattern_to_expr)
                            .collect::<Option<Vec<_>>>()
                            .expect("non-pattern sequence"),
                    )),
                    false,
                )
            }
        }
        spec::Expr::StructLit { name, fields } => {
            let mut has_pattern = false;
            let fields = fields
                .into_iter()
                .map(|field| {
                    let (value, field_has_pattern) = expr_to_value_pattern(field.value, binders);
                    has_pattern |= field_has_pattern;
                    ValuePatternStructField {
                        name: field.name,
                        value,
                    }
                })
                .collect::<Vec<_>>();
            if has_pattern {
                (ValuePattern::StructLit { name, fields }, true)
            } else {
                (
                    ValuePattern::Expr(spec::Expr::StructLit {
                        name,
                        fields: fields
                            .into_iter()
                            .map(|field| {
                                Some(spec::StructLitField {
                                    name: field.name,
                                    value: value_pattern_to_expr(field.value)?,
                                })
                            })
                            .collect::<Option<Vec<_>>>()
                            .expect("non-pattern struct"),
                    }),
                    false,
                )
            }
        }
        spec::Expr::Call {
            func,
            type_args,
            args,
        } => {
            let mut has_pattern = false;
            let args = args
                .into_iter()
                .map(|arg| {
                    let (pattern, arg_has_pattern) = expr_to_value_pattern(arg, binders);
                    has_pattern |= arg_has_pattern;
                    pattern
                })
                .collect::<Vec<_>>();
            if has_pattern {
                (
                    ValuePattern::Call {
                        func,
                        type_args,
                        args,
                    },
                    true,
                )
            } else {
                (
                    ValuePattern::Expr(spec::Expr::Call {
                        func,
                        type_args,
                        args: args
                            .into_iter()
                            .map(value_pattern_to_expr)
                            .collect::<Option<Vec<_>>>()
                            .expect("non-pattern call"),
                    }),
                    false,
                )
            }
        }
        other => (ValuePattern::Expr(other), false),
    }
}

fn value_pattern_to_expr(pattern: ValuePattern) -> Option<spec::Expr> {
    match pattern {
        ValuePattern::Expr(expr) => Some(expr),
        _ => None,
    }
}

fn parse_raw_assert_expr(text: &str, span: Span) -> Result<spec::Expr, DirectiveError> {
    spec::parse_source_expr("raw assert", text.trim()).map_err(|err| DirectiveError {
        span,
        message: render_parse_error(DirectiveKind::RawAssert, err),
    })
}

fn strip_enclosing_parens(mut text: &str) -> &str {
    loop {
        let trimmed = text.trim();
        if !(trimmed.starts_with('(') && trimmed.ends_with(')')) {
            return trimmed;
        }
        if matching_outer_parens(trimmed) {
            text = &trimmed[1..trimmed.len() - 1];
        } else {
            return trimmed;
        }
    }
}

fn matching_outer_parens(text: &str) -> bool {
    let mut depth = 0usize;
    for (index, ch) in text.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && index + ch.len_utf8() != text.len() {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

fn top_level_star(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (index, ch) in text.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            '*' if depth == 0 && index != 0 => return Some(index),
            _ => {}
        }
    }
    None
}

fn top_level_points_to_arrow(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut index = 0usize;
    while index < text.len() {
        let ch = text[index..].chars().next().expect("valid char boundary");
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            '|' if depth == 0 && text[index..].starts_with("|->") => return Some(index),
            _ => {}
        }
        index += ch.len_utf8();
    }
    None
}

fn atom_args<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    let rest = text.strip_prefix(name)?.trim_start();
    let args = rest.strip_prefix('(')?.strip_suffix(')')?;
    Some(args)
}

fn split_top_level_args(text: &str, span: Span) -> Result<Vec<&str>, DirectiveError> {
    let mut args = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (index, ch) in text.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                args.push(text[start..index].trim());
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }
    args.push(text[start..].trim());
    if args.iter().any(|arg| arg.is_empty()) {
        return Err(DirectiveError {
            span,
            message: "raw pattern arguments must not be empty".to_owned(),
        });
    }
    Ok(args)
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

#[cfg(test)]
pub(crate) fn function_contract_lines_before_item(
    source: &str,
    item_line: usize,
) -> Option<Vec<String>> {
    function_contract_comment_lines_before_line(source, item_line)
        .map(|lines| lines.into_iter().map(|line| line.render()).collect())
}

#[cfg(test)]
pub(crate) fn function_contract_lines_before_body(
    source: &str,
    body_line: usize,
) -> Option<Vec<String>> {
    function_contract_comment_lines_before_line(source, body_line)
        .map(|lines| lines.into_iter().map(|line| line.render()).collect())
}

type SpecCommentLine = spec::SpecComment;

#[cfg(test)]
impl SpecCommentLine {
    fn render(self) -> String {
        format!("//@ {}", self.text)
    }
}

#[derive(Debug)]
struct DirectiveText {
    kind: DirectiveKind,
    text: String,
    line_no: usize,
    line_text: String,
    start_offset: usize,
}

fn function_contract_comment_lines_before_item(
    source: &str,
    item_line: usize,
) -> Option<Vec<SpecCommentLine>> {
    function_contract_comment_lines_before_line(source, item_line)
}

fn function_contract_comment_lines_before_body(
    source: &str,
    body_line: usize,
) -> Option<Vec<SpecCommentLine>> {
    function_contract_comment_lines_before_line(source, body_line)
}

fn function_contract_comment_lines_before_line(
    source: &str,
    line_no: usize,
) -> Option<Vec<SpecCommentLine>> {
    if line_no <= 1 {
        return None;
    }

    let comments = collect_line_spec_comments(source);
    let mut idx = comments
        .iter()
        .rposition(|comment| comment.end_line < line_no)?;
    if !physical_lines_between_are_blank(source, comments[idx].end_line + 1, line_no - 1) {
        return None;
    }

    let mut block = Vec::new();
    loop {
        let comment = &comments[idx];
        block.push(comment.clone());
        if idx == 0 {
            break;
        }
        let previous = &comments[idx - 1];
        if !physical_lines_between_are_blank(source, previous.end_line + 1, comment.start_line - 1)
        {
            break;
        }
        idx -= 1;
    }
    block.reverse();
    Some(block)
}

fn physical_lines_between_are_blank(source: &str, start_line: usize, end_line: usize) -> bool {
    if start_line > end_line {
        return true;
    }
    source
        .lines()
        .enumerate()
        .filter(|(index, _)| {
            let line_no = index + 1;
            start_line <= line_no && line_no <= end_line
        })
        .all(|(_, line)| line.trim().is_empty())
}

fn collect_line_spec_comments(source: &str) -> Vec<SpecCommentLine> {
    let mut comments = Vec::new();
    let mut ghost_item = Vec::new();
    for comment in spec::collect_spec_comments(source) {
        if ghost_item.is_empty() && spec::is_ghost_item_block(&comment.text) {
            ghost_item.push(comment);
            if spec::is_complete_ghost_item_comment(&spec::spec_comment_group_text(&ghost_item)) {
                ghost_item.clear();
            }
            continue;
        }
        if !ghost_item.is_empty() {
            ghost_item.push(comment);
            if spec::is_complete_ghost_item_comment(&spec::spec_comment_group_text(&ghost_item)) {
                ghost_item.clear();
            }
            continue;
        }
        comments.push(comment);
    }
    comments
}

fn contract_directive_entries(
    comments: &[SpecCommentLine],
    span: Span,
) -> Result<Vec<DirectiveText>, DirectiveError> {
    let logical = logical_directive_texts(comments, contract_comment_kind);
    let mut entries = Vec::new();
    for directive in logical {
        entries.extend(split_directive_text(
            directive,
            contract_comment_kind,
            span,
        )?);
    }
    Ok(entries)
}

fn statement_directive_entries(
    comments: &[SpecCommentLine],
    position_error: DirectiveError,
) -> Result<Vec<DirectiveText>, DirectiveError> {
    let mut entries = Vec::new();
    for comment in comments {
        if matches_reserved_statement_directive(&comment.text)
            && !matches!(
                classify_statement_directive(&comment.text),
                Some(
                    DirectiveKind::Assert
                        | DirectiveKind::Assume
                        | DirectiveKind::RawAssert
                        | DirectiveKind::Let
                )
            )
        {
            return Err(position_error);
        }

        if let Some(kind) = classify_statement_directive(&comment.text) {
            let text = comment.text[kind.keyword().len()..].trim().to_owned();
            entries.push(DirectiveText {
                kind,
                text,
                line_no: comment.line_no,
                line_text: comment.line_text.clone(),
                start_offset: comment.start_offset,
            });
        } else if let Some(last) = entries.last_mut()
            && !last.text.trim_end().ends_with(';')
        {
            if !last.text.is_empty() {
                last.text.push(' ');
            }
            last.text.push_str(comment.text.trim());
            last.line_text.push(' ');
            last.line_text.push_str(comment.line_text.trim());
        } else {
            entries.push(DirectiveText {
                kind: DirectiveKind::LemmaCall,
                text: comment.text.trim().to_owned(),
                line_no: comment.line_no,
                line_text: comment.line_text.clone(),
                start_offset: comment.start_offset,
            });
        }
    }
    Ok(entries)
}

fn loop_invariant_entries(source: &str, span: Span) -> Result<Vec<DirectiveText>, DirectiveError> {
    let comments = collect_line_spec_comments(source);
    let logical = logical_directive_texts(&comments, invariant_comment_kind);
    let mut entries = Vec::new();
    for directive in logical {
        entries.extend(split_directive_text(
            directive,
            invariant_comment_kind,
            span,
        )?);
    }
    Ok(entries)
}

fn logical_directive_texts(
    comments: &[SpecCommentLine],
    classify: fn(&str) -> Option<DirectiveKind>,
) -> Vec<DirectiveText> {
    let mut entries: Vec<DirectiveText> = Vec::new();
    for comment in comments {
        if let Some(kind) = classify(&comment.text) {
            let text = comment.text[kind.keyword().len()..].trim().to_owned();
            entries.push(DirectiveText {
                kind,
                text,
                line_no: comment.line_no,
                line_text: comment.line_text.clone(),
                start_offset: comment.start_offset,
            });
        } else if let Some(last) = entries.last_mut() {
            if !last.text.is_empty() {
                last.text.push(' ');
            }
            last.text.push_str(comment.text.trim());
            last.line_text.push(' ');
            last.line_text.push_str(comment.line_text.trim());
        }
    }
    entries
}

fn split_directive_text(
    directive: DirectiveText,
    classify: fn(&str) -> Option<DirectiveKind>,
    span: Span,
) -> Result<Vec<DirectiveText>, DirectiveError> {
    let mut entries = Vec::new();
    let mut kind = directive.kind;
    let mut text = directive.text.as_str();
    loop {
        let Some((next_at, next_kind)) = find_next_directive_keyword(text, classify) else {
            entries.push(DirectiveText {
                kind,
                text: text.trim().to_owned(),
                line_no: directive.line_no,
                line_text: directive.line_text.clone(),
                start_offset: directive.start_offset,
            });
            return Ok(entries);
        };
        entries.push(DirectiveText {
            kind,
            text: text[..next_at].trim().to_owned(),
            line_no: directive.line_no,
            line_text: directive.line_text.clone(),
            start_offset: directive.start_offset,
        });
        let next_start = next_at + next_kind.keyword().len();
        if next_start > text.len() {
            return Err(DirectiveError {
                span,
                message: "empty directive".to_owned(),
            });
        }
        kind = next_kind;
        text = &text[next_start..];
    }
}

fn find_next_directive_keyword(
    text: &str,
    classify: fn(&str) -> Option<DirectiveKind>,
) -> Option<(usize, DirectiveKind)> {
    let mut depth = 0usize;
    let mut previous_boundary = true;
    for (index, ch) in text.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 && previous_boundary {
            let rest = &text[index..];
            if let Some(kind) = classify(rest)
                && index != 0
            {
                return Some((index, kind));
            }
        }
        previous_boundary = ch.is_whitespace() || ch == ';';
    }
    None
}

fn contract_comment_kind(text: &str) -> Option<DirectiveKind> {
    directive_kind_prefix(
        text,
        &[
            DirectiveKind::RawReq,
            DirectiveKind::RawEns,
            DirectiveKind::Req,
            DirectiveKind::Ens,
            DirectiveKind::Let,
        ],
    )
}

fn invariant_comment_kind(text: &str) -> Option<DirectiveKind> {
    directive_kind_prefix(text, &[DirectiveKind::Inv])
}

fn directive_kind_prefix(text: &str, kinds: &[DirectiveKind]) -> Option<DirectiveKind> {
    kinds.iter().copied().find(|kind| {
        text.strip_prefix(kind.keyword())
            .is_some_and(|rest| rest.chars().next().is_none_or(|ch| ch.is_whitespace()))
    })
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
        let entries = loop_invariant_entries(prefix_source, entry_span)?;
        if entries.is_empty() {
            return Err(self.missing_invariant_error(loop_expr, loop_body));
        };
        if entries.len() > 1 {
            return Err(self.multiple_invariant_error(entry_span));
        }
        let entry = entries.into_iter().next().expect("entry present");
        if !source_contains_only_spec_comments(&prefix_source[entry.start_offset..]) {
            return Err(self.invariant_position_error(entry_span));
        }

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
            entry.start_offset,
        );
        let span_text = display_line_span(&file_name, line_no, &entry.line_text);
        let payload = parse_directive_payload(DirectiveKind::Inv, entry.text.trim(), entry_span)?;
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
        let Some(first_directive) = first_spec_comment_pos(body) else {
            return Ok(Vec::new());
        };
        let body = &body[first_directive..];
        if !source_contains_only_spec_comments(body) {
            return Err(
                self.statement_directive_position_error(anchor_span, DirectiveKind::LemmaCall)
            );
        }

        let comment_lines = collect_line_spec_comments(body);
        if comment_lines.is_empty() {
            return Err(
                self.statement_directive_position_error(anchor_span, DirectiveKind::LemmaCall)
            );
        }

        let mut found = Vec::new();
        for entry in statement_directive_entries(
            &comment_lines,
            self.statement_directive_position_error(anchor_span, DirectiveKind::LemmaCall),
        )? {
            let directive_pos = first_directive + entry.start_offset;
            let payload = parse_directive_payload(entry.kind, entry.text.trim(), anchor_span)?;
            let line_no = directive_line_number(line_anchor, source, directive_pos);
            let span_text = display_line_span(file_name, line_no, &entry.line_text);
            found.push(FunctionDirective {
                kind: entry.kind,
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

fn trim_terminal_anchor_suffix(source: &str) -> &str {
    source.trim_end_matches(|c: char| c.is_whitespace() || c == '}')
}

fn first_spec_comment_pos(source: &str) -> Option<usize> {
    match (source.find("//@"), source.find("/*@")) {
        (Some(line), Some(block)) => Some(line.min(block)),
        (Some(line), None) => Some(line),
        (None, Some(block)) => Some(block),
        (None, None) => None,
    }
}

fn source_contains_only_spec_comments(source: &str) -> bool {
    let mut in_block = false;
    for line in source.lines() {
        let trimmed = line.trim_start();
        if in_block {
            if trimmed.contains("*/") {
                in_block = false;
            }
            continue;
        }
        if trimmed.trim_end().is_empty() || trimmed.starts_with("//@") {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("/*@") {
            in_block = !rest.contains("*/");
            continue;
        }
        return false;
    }
    true
}

fn classify_statement_directive(text: &str) -> Option<DirectiveKind> {
    directive_kind_prefix(
        text,
        &[
            DirectiveKind::Assert,
            DirectiveKind::Assume,
            DirectiveKind::RawAssert,
            DirectiveKind::Let,
        ],
    )
}

fn matches_reserved_statement_directive(text: &str) -> bool {
    directive_kind_prefix(
        text,
        &[
            DirectiveKind::Assert,
            DirectiveKind::Assume,
            DirectiveKind::RawAssert,
            DirectiveKind::Inv,
            DirectiveKind::Req,
            DirectiveKind::Ens,
            DirectiveKind::Let,
        ],
    )
    .is_some()
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

    #[test]
    fn splits_doc_style_function_contract_comments() {
        let source =
            "fn callee() -> i32\n//@ req true &&\n/*@ true */\n//@ ens result == 3\n{\n    2\n}\n";
        let lines = super::function_contract_comment_lines_before_body(source, 5).unwrap();
        let entries = super::contract_directive_entries(&lines, rustc_span::DUMMY_SP).unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].kind, super::DirectiveKind::Req);
        assert_eq!(entries[0].text, "true && true");
        assert_eq!(entries[1].kind, super::DirectiveKind::Ens);
        assert_eq!(entries[1].text, "result == 3");
    }

    #[test]
    fn splits_inline_req_ens_contract_comment() {
        let source = "fn callee() -> i32\n//@ req true ens result == 3\n{\n    2\n}\n";
        let lines = super::function_contract_comment_lines_before_body(source, 3).unwrap();
        let entries = super::contract_directive_entries(&lines, rustc_span::DUMMY_SP).unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].kind, super::DirectiveKind::Req);
        assert_eq!(entries[0].text, "true");
        assert_eq!(entries[1].kind, super::DirectiveKind::Ens);
        assert_eq!(entries[1].text, "result == 3");
    }
}
