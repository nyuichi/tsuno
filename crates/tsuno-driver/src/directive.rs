use std::ops::ControlFlow;

use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Block, Expr as HirExpr, ExprKind, HirId, LoopSource, MatchSource, Stmt, StmtKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;

use crate::spec::{
    self, BinaryOp, EnumCtorDef, EnumDef, Expr, GhostBlock, GhostMatchArm, GhostStmt, IntLiteral,
    IntSuffix, LemmaDef, MatchArm, MatchBinding, MatchPattern, PureFnDef, PureFnParam,
    ResourceAssertion, ResourcePattern, RustTypeExpr, SpecTy, StructDef, StructFieldTy,
    StructLitField, UnaryOp, ValuePattern, ValuePatternStructField, provenance_spec_ty,
    ptr_spec_ty,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveKind {
    Req,
    Ens,
    Let,
    Inv,
    Assert,
    Assume,
    ResourceAssert,
    ResourceReq,
    ResourceEns,
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
            Self::ResourceAssert => "resource assert",
            Self::ResourceReq => "resource req",
            Self::ResourceEns => "resource ens",
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
    ResourceAssert(ResourceAssertion),
    LemmaCall(spec::Expr),
}

impl FunctionDirective {
    pub fn expr(&self) -> &spec::Expr {
        match &self.payload {
            DirectivePayload::Predicate(expr) | DirectivePayload::LemmaCall(expr) => expr,
            DirectivePayload::Let { value, .. } => value,
            DirectivePayload::ResourceAssert(_) => {
                panic!("resource assertion directive has no single expression")
            }
        }
    }

    pub fn resource_assertion(&self) -> Option<&ResourceAssertion> {
        match &self.payload {
            DirectivePayload::ResourceAssert(assertion) => Some(assertion),
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
        return parse_statement_expr("lemma call", text.trim())
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
        DirectiveKind::ResourceAssert | DirectiveKind::ResourceReq | DirectiveKind::ResourceEns
    ) {
        return parse_resource_assert_directive(text, span);
    }
    let parsed = match kind {
        DirectiveKind::Assert | DirectiveKind::Assume => parse_statement_expr(kind.keyword(), text),
        _ => parse_source_expr(kind.keyword(), text),
    };
    parsed
        .map_err(|err| DirectiveError {
            span,
            message: render_parse_error(kind, err),
        })
        .map(DirectivePayload::Predicate)
}

fn parse_resource_assert_directive(
    text: &str,
    span: Span,
) -> Result<DirectivePayload, DirectiveError> {
    parse_resource_assertion(text)
        .map(DirectivePayload::ResourceAssert)
        .map_err(|err| DirectiveError {
            span,
            message: err.to_string(),
        })
}

pub fn parse_resource_assertion(text: &str) -> Result<ResourceAssertion, ParseError> {
    let text = text.trim().strip_suffix(';').unwrap_or(text.trim()).trim();
    let (pattern, condition) = split_resource_assert_where(text);
    let pattern = parse_resource_pattern(pattern)?;
    let condition = match condition {
        Some(condition) => parse_resource_expr(condition)?,
        None => spec::Expr::Bool(true),
    };
    Ok(ResourceAssertion { pattern, condition })
}

fn parse_resource_pattern(text: &str) -> Result<ResourcePattern, ParseError> {
    let text = strip_enclosing_parens(text.trim());
    if let Some(index) = top_level_star(text) {
        let lhs = parse_resource_pattern(&text[..index])?;
        let rhs = parse_resource_pattern(&text[index + 1..])?;
        return Ok(ResourcePattern::Star(Box::new(lhs), Box::new(rhs)));
    }
    if let Some(index) = top_level_points_to_arrow(text) {
        return parse_points_to_sugar(&text[..index], &text[index + "|->".len()..]);
    }
    if let Some(args) = atom_args(text, "PointsTo") {
        let args = split_top_level_args(args)?;
        if args.len() != 3 {
            return Err(ParseError::new(
                "`PointsTo` resource pattern expects three arguments",
            ));
        }
        return Ok(ResourcePattern::PointsTo {
            addr: parse_resource_expr(args[0])?,
            ty: parse_resource_expr(args[1])?,
            value: parse_value_pattern(args[2])?,
        });
    }
    if let Some(args) = atom_args(text, "DeallocToken") {
        let args = split_top_level_args(args)?;
        if args.len() != 3 {
            return Err(ParseError::new(
                "`DeallocToken` resource pattern expects three arguments",
            ));
        }
        return Ok(ResourcePattern::DeallocToken {
            base: parse_resource_expr(args[0])?,
            size: parse_resource_expr(args[1])?,
            alignment: parse_resource_expr(args[2])?,
        });
    }
    Err(ParseError::new(
        "resource assertion must be a `PointsTo`, `DeallocToken`, or `*` pattern",
    ))
}

fn parse_points_to_sugar(lhs: &str, rhs: &str) -> Result<ResourcePattern, ParseError> {
    let lhs = strip_enclosing_parens(lhs.trim());
    let Some(pointer) = lhs.strip_prefix('*').map(str::trim) else {
        return Err(ParseError::new(
            "`|->` resource pattern must have the form `*ptr |-> value`",
        ));
    };
    if !is_ident(pointer) {
        return Err(ParseError::new(
            "`|->` resource pattern pointer must be a Rust local name",
        ));
    }
    Ok(ResourcePattern::PointsToSugar {
        pointer: pointer.to_owned(),
        value: parse_value_pattern(rhs)?,
    })
}

fn split_resource_assert_where(text: &str) -> (&str, Option<&str>) {
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

fn parse_value_pattern(text: &str) -> Result<ValuePattern, ParseError> {
    let (rewritten, binders) = rewrite_pattern_binders(text)?;
    let expr = parse_resource_expr(&rewritten)?;
    Ok(expr_to_value_pattern(expr, &binders).0)
}

fn rewrite_pattern_binders(text: &str) -> Result<(String, Vec<(String, String)>), ParseError> {
    let mut rewritten = String::with_capacity(text.len());
    let mut binders = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((_, ch)) = chars.next() {
        if ch != '?' {
            rewritten.push(ch);
            continue;
        }
        let Some((_, first)) = chars.peek().copied() else {
            return Err(ParseError::new("resource pattern binder must be `?ident`"));
        };
        if !(first == '_' || first.is_ascii_alphabetic()) {
            return Err(ParseError::new("resource pattern binder must be `?ident`"));
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
        let placeholder = format!("__tsuno_resource_binder_{}", binders.len());
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

fn parse_resource_expr(text: &str) -> Result<spec::Expr, ParseError> {
    parse_source_expr("resource assert", text.trim())
        .map_err(|err| ParseError::new(render_parse_error(DirectiveKind::ResourceAssert, err)))
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

fn split_top_level_args(text: &str) -> Result<Vec<&str>, ParseError> {
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
        return Err(ParseError::new(
            "resource pattern arguments must not be empty",
        ));
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
    let value = parse_source_expr("let", value.trim()).map_err(|err| DirectiveError {
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

fn render_parse_error(kind: DirectiveKind, err: ParseError) -> String {
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

type SpecCommentLine = SpecComment;

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
    for comment in collect_spec_comments(source) {
        if ghost_item.is_empty() && is_ghost_item_block(&comment.text) {
            ghost_item.push(comment);
            if is_complete_ghost_item_comment(&spec_comment_group_text(&ghost_item)) {
                ghost_item.clear();
            }
            continue;
        }
        if !ghost_item.is_empty() {
            ghost_item.push(comment);
            if is_complete_ghost_item_comment(&spec_comment_group_text(&ghost_item)) {
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
                        | DirectiveKind::ResourceAssert
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
            DirectiveKind::ResourceReq,
            DirectiveKind::ResourceEns,
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
        loop_expr: &'a HirExpr<'a>,
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
        loop_expr: &'a HirExpr<'a>,
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

    fn first_loop_control_expr(&self, body: &'a Block<'a>) -> Option<&'a HirExpr<'a>> {
        if let Some(expr) = body.expr {
            return Some(expr);
        }
        body.stmts.iter().find_map(stmt_expr)
    }

    fn missing_invariant_error(
        &self,
        loop_expr: &'a HirExpr<'a>,
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

    fn visit_expr(&mut self, expr: &'tcx HirExpr<'tcx>) -> Self::Result {
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

fn stmt_expr<'tcx>(stmt: &'tcx Stmt<'tcx>) -> Option<&'tcx HirExpr<'tcx>> {
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
            DirectiveKind::ResourceAssert,
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
            DirectiveKind::ResourceAssert,
            DirectiveKind::Inv,
            DirectiveKind::Req,
            DirectiveKind::Ens,
            DirectiveKind::Let,
        ],
    )
    .is_some()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    message: String,
}

impl ParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Clone)]
pub struct SpecComment {
    pub text: String,
    pub line_no: usize,
    pub line_text: String,
    pub start_line: usize,
    pub end_line: usize,
    pub start_offset: usize,
}

pub fn is_ghost_item_block(text: &str) -> bool {
    let trimmed = text.trim_start();
    trimmed.starts_with("fn ")
        || trimmed.starts_with("unsafe fn ")
        || trimmed.starts_with("enum ")
        || trimmed.starts_with("struct ")
}

pub fn is_complete_ghost_item_comment(text: &str) -> bool {
    let mut depth = 0usize;
    let mut saw_brace = false;
    for ch in text.chars() {
        match ch {
            '{' => {
                saw_brace = true;
                depth += 1;
            }
            '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    saw_brace && depth == 0
}

pub fn collect_spec_comments(source: &str) -> Vec<SpecComment> {
    let physical_lines: Vec<_> = source.lines().collect();
    let mut comments = Vec::new();
    let mut index = 0;
    let mut line_offset = 0;
    while index < physical_lines.len() {
        let line = physical_lines[index];
        let line_comment = line.find("//@");
        let block_comment = line.find("/*@");
        let first_comment = match (line_comment, block_comment) {
            (Some(line), Some(block)) => Some(line.min(block)),
            (Some(line), None) => Some(line),
            (None, Some(block)) => Some(block),
            (None, None) => None,
        };
        let Some(comment_col) = first_comment else {
            line_offset += line.len() + 1;
            index += 1;
            continue;
        };
        let comment = &line[comment_col..];
        if let Some(text) = comment.strip_prefix("//@") {
            let start_offset = line_offset + comment_col;
            comments.push(SpecComment {
                text: text.trim().to_owned(),
                line_no: index + 1,
                line_text: line.trim_end().to_owned(),
                start_line: index + 1,
                end_line: index + 1,
                start_offset,
            });
            line_offset += line.len() + 1;
            index += 1;
            continue;
        }
        if let Some(first) = comment.strip_prefix("/*@") {
            let start_line = index + 1;
            let start_offset = line_offset + comment_col;
            let mut parts = Vec::new();
            let mut line_text = line.trim_end().to_owned();
            let mut rest = first;
            loop {
                if let Some(end) = rest.find("*/") {
                    parts.push(rest[..end].trim().to_owned());
                    let text = parts.join("\n");
                    comments.push(SpecComment {
                        text: text.trim().to_owned(),
                        line_no: start_line,
                        line_text,
                        start_line,
                        end_line: index + 1,
                        start_offset,
                    });
                    line_offset += physical_lines[index].len() + 1;
                    index += 1;
                    break;
                }
                parts.push(rest.trim().to_owned());
                line_offset += physical_lines[index].len() + 1;
                index += 1;
                if index >= physical_lines.len() {
                    break;
                }
                rest = physical_lines[index];
                line_text.push(' ');
                line_text.push_str(rest.trim_end());
            }
            continue;
        }
    }
    comments
}

pub fn spec_comment_group_text(group: &[SpecComment]) -> String {
    group
        .iter()
        .map(|comment| comment.text.as_str())
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
pub fn parse_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    parse_source_expr(kind, text)
}

pub fn parse_source_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    parse_source_expr_with_type_params(kind, text, &[])
}

fn parse_source_expr_with_type_params(
    kind: &str,
    text: &str,
    type_params: &[String],
) -> Result<Expr, ParseError> {
    parse_raw_expr_with_type_params(kind, text.trim(), type_params)
}

pub fn parse_statement_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    let text = text.trim();
    let Some(text) = text.strip_suffix(';') else {
        return Err(ParseError::new(format!(
            "failed to parse //@ {kind} predicate: expected trailing `;`"
        )));
    };
    parse_source_expr(kind, text.trim_end())
}

#[cfg(test)]
pub fn parse_raw_expr(_kind: &str, text: &str) -> Result<Expr, ParseError> {
    parse_raw_expr_with_type_params(_kind, text, &[])
}

fn parse_spec_ty_text_with_params(
    text: &str,
    type_params: &[String],
) -> Result<SpecTy, ParseError> {
    let mut parser = Parser::new(text)?;
    parser.type_params = type_params.to_vec();
    let ty = parser.parse_spec_ty()?;
    parser.expect_end()?;
    Ok(ty)
}

fn parse_raw_expr_with_type_params(
    _kind: &str,
    text: &str,
    type_params: &[String],
) -> Result<Expr, ParseError> {
    let mut parser = Parser::new(text)?;
    parser.type_params = type_params.to_vec();
    let expr = parser.parse_expr()?;
    parser.expect_end()?;
    Ok(expr)
}

fn parse_raw_match_pattern(text: &str) -> Result<MatchPattern, ParseError> {
    let mut parser = Parser::new(text)?;
    let pattern = parser
        .parse_match_arm_pattern()?
        .ok_or_else(|| ParseError::new("expected match arm pattern"))?;
    parser.expect_end()?;
    Ok(pattern)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Int(IntLiteral),
    Bool(bool),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Dot,
    Colon,
    ColonColon,
    FatArrow,
    Question,
    Concat,
    Plus,
    Minus,
    Star,
    Bang,
    Amp,
    EqEq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    AndAnd,
    OrOr,
}

fn lex_expr(text: &str) -> Result<Vec<Token>, ParseError> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.peek().copied() {
        match ch {
            ' ' | '\t' | '\r' | '\n' => {
                chars.next();
            }
            '0'..='9' => {
                let mut digits = String::new();
                while let Some(next) = chars.peek().copied() {
                    if next.is_ascii_digit() {
                        digits.push(next);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if matches!(chars.peek(), Some(next) if next.is_ascii_alphabetic()) {
                    let mut suffix = String::new();
                    while let Some(next) = chars.peek().copied() {
                        if next.is_ascii_alphanumeric() || next == '_' {
                            suffix.push(next);
                            chars.next();
                        } else {
                            break;
                        }
                    }
                    let suffix = parse_int_suffix(&suffix)?;
                    tokens.push(Token::Int(IntLiteral {
                        digits,
                        suffix: Some(suffix),
                    }));
                } else {
                    tokens.push(Token::Int(IntLiteral {
                        digits,
                        suffix: None,
                    }));
                }
            }
            'a'..='z' | 'A'..='Z' | '_' => {
                let mut ident = String::new();
                while let Some(next) = chars.peek().copied() {
                    if next.is_ascii_alphanumeric() || next == '_' {
                        ident.push(next);
                        chars.next();
                    } else {
                        break;
                    }
                }
                match ident.as_str() {
                    "true" => tokens.push(Token::Bool(true)),
                    "false" => tokens.push(Token::Bool(false)),
                    _ => tokens.push(Token::Ident(ident)),
                }
            }
            '(' => {
                chars.next();
                tokens.push(Token::LParen);
            }
            ')' => {
                chars.next();
                tokens.push(Token::RParen);
            }
            '{' => {
                chars.next();
                tokens.push(Token::LBrace);
            }
            '}' => {
                chars.next();
                tokens.push(Token::RBrace);
            }
            '[' => {
                chars.next();
                tokens.push(Token::LBracket);
            }
            ']' => {
                chars.next();
                tokens.push(Token::RBracket);
            }
            ',' => {
                chars.next();
                tokens.push(Token::Comma);
            }
            '.' => {
                chars.next();
                tokens.push(Token::Dot);
            }
            ':' => {
                chars.next();
                if chars.peek() == Some(&':') {
                    chars.next();
                    tokens.push(Token::ColonColon);
                } else {
                    tokens.push(Token::Colon);
                }
            }
            '?' => {
                chars.next();
                tokens.push(Token::Question);
            }
            '+' => {
                chars.next();
                if chars.peek() == Some(&'+') {
                    chars.next();
                    tokens.push(Token::Concat);
                } else {
                    tokens.push(Token::Plus);
                }
            }
            '-' => {
                chars.next();
                tokens.push(Token::Minus);
            }
            '*' => {
                chars.next();
                tokens.push(Token::Star);
            }
            '!' => {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    tokens.push(Token::Ne);
                } else {
                    tokens.push(Token::Bang);
                }
            }
            '=' => {
                chars.next();
                if chars.peek() == Some(&'>') {
                    chars.next();
                    tokens.push(Token::FatArrow);
                } else if chars.next() == Some('=') {
                    tokens.push(Token::EqEq);
                } else {
                    return Err(ParseError::new("unexpected `=` in spec expression"));
                }
            }
            '>' => {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    tokens.push(Token::Ge);
                } else {
                    tokens.push(Token::Gt);
                }
            }
            '<' => {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    tokens.push(Token::Le);
                } else {
                    tokens.push(Token::Lt);
                }
            }
            '&' => {
                chars.next();
                if chars.peek() == Some(&'&') {
                    chars.next();
                    tokens.push(Token::AndAnd);
                } else {
                    tokens.push(Token::Amp);
                }
            }
            '|' => {
                chars.next();
                if chars.next() == Some('|') {
                    tokens.push(Token::OrOr);
                } else {
                    return Err(ParseError::new("unexpected `|` in spec expression"));
                }
            }
            _ => {
                return Err(ParseError::new(format!(
                    "unexpected character `{ch}` in spec expression"
                )));
            }
        }
    }
    Ok(tokens)
}

fn parse_int_suffix(text: &str) -> Result<IntSuffix, ParseError> {
    match text {
        "Nat" => Ok(IntSuffix::Nat),
        "i8" => Ok(IntSuffix::I8),
        "i16" => Ok(IntSuffix::I16),
        "i32" => Ok(IntSuffix::I32),
        "i64" => Ok(IntSuffix::I64),
        "isize" => Ok(IntSuffix::Isize),
        "u8" => Ok(IntSuffix::U8),
        "u16" => Ok(IntSuffix::U16),
        "u32" => Ok(IntSuffix::U32),
        "u64" => Ok(IntSuffix::U64),
        "usize" => Ok(IntSuffix::Usize),
        _ => Err(ParseError::new(format!(
            "unsupported integer literal suffix `{text}` in spec expression"
        ))),
    }
}

struct Parser {
    tokens: Vec<Token>,
    cursor: usize,
    type_params: Vec<String>,
}

impl Parser {
    fn new(text: &str) -> Result<Self, ParseError> {
        Ok(Self {
            tokens: lex_expr(text)?,
            cursor: 0,
            type_params: Vec::new(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_or()
    }

    fn expect_end(&self) -> Result<(), ParseError> {
        if self.cursor == self.tokens.len() {
            Ok(())
        } else {
            Err(ParseError::new(
                "unexpected trailing tokens in spec expression",
            ))
        }
    }

    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_and()?;
        while self.eat(&Token::OrOr) {
            let rhs = self.parse_and()?;
            expr = Expr::Binary {
                op: BinaryOp::Or,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_eq()?;
        while self.eat(&Token::AndAnd) {
            let rhs = self.parse_eq()?;
            expr = Expr::Binary {
                op: BinaryOp::And,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_eq(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_cmp()?;
        loop {
            let op = if self.eat(&Token::EqEq) {
                Some(BinaryOp::Eq)
            } else if self.eat(&Token::Ne) {
                Some(BinaryOp::Ne)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_cmp()?;
            expr = Expr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_cmp(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_concat()?;
        loop {
            let op = if self.eat(&Token::Lt) {
                Some(BinaryOp::Lt)
            } else if self.eat(&Token::Le) {
                Some(BinaryOp::Le)
            } else if self.eat(&Token::Gt) {
                Some(BinaryOp::Gt)
            } else if self.eat(&Token::Ge) {
                Some(BinaryOp::Ge)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_concat()?;
            expr = Expr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_concat(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_add()?;
        while self.eat(&Token::Concat) {
            let rhs = self.parse_add()?;
            expr = Expr::Binary {
                op: BinaryOp::Concat,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_add(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_mul()?;
        loop {
            let op = if self.eat(&Token::Plus) {
                Some(BinaryOp::Add)
            } else if self.eat(&Token::Minus) {
                Some(BinaryOp::Sub)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_mul()?;
            expr = Expr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_mul(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_unary()?;
        while self.eat(&Token::Star) {
            let rhs = self.parse_unary()?;
            expr = Expr::Binary {
                op: BinaryOp::Mul,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        if self.eat(&Token::Bang) {
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                arg: Box::new(self.parse_unary()?),
            });
        }
        if self.eat(&Token::Minus) {
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                arg: Box::new(self.parse_unary()?),
            });
        }
        if self.eat(&Token::Star) {
            return Ok(Expr::Deref {
                base: Box::new(self.parse_unary()?),
            });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;
        loop {
            if self.eat(&Token::Dot) {
                expr = match self.next() {
                    Some(Token::Int(value)) if value.as_unsuffixed_usize().is_some() => {
                        Expr::TupleField {
                            base: Box::new(expr),
                            index: value
                                .as_unsuffixed_usize()
                                .expect("checked tuple field index"),
                        }
                    }
                    Some(Token::Ident(ident)) => Expr::Field {
                        base: Box::new(expr),
                        name: ident.clone(),
                    },
                    _ => {
                        return Err(ParseError::new(
                            "unsupported field access in spec expression",
                        ));
                    }
                };
                continue;
            }
            if self.eat(&Token::LBracket) {
                let index = self.parse_expr()?;
                self.expect(&Token::RBracket)?;
                expr = Expr::Index {
                    base: Box::new(expr),
                    index: Box::new(index),
                };
                continue;
            }
            break;
        }
        Ok(expr)
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut args = Vec::new();
        self.expect(&Token::LParen)?;
        if self.eat(&Token::RParen) {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
            if self.eat(&Token::RParen) {
                return Ok(args);
            }
            self.expect(&Token::Comma)?;
        }
    }

    fn parse_match_bindings(&mut self) -> Result<Vec<MatchBinding>, ParseError> {
        let mut bindings = Vec::new();
        self.expect(&Token::LParen)?;
        if self.eat(&Token::RParen) {
            return Ok(bindings);
        }
        loop {
            bindings.push(match self.next().cloned() {
                Some(Token::Ident(name)) if name == "_" => MatchBinding::Wildcard,
                Some(Token::Ident(name)) => MatchBinding::Var(name),
                _ => {
                    return Err(ParseError::new(
                        "expected a variable name or `_` in match pattern",
                    ));
                }
            });
            if self.eat(&Token::RParen) {
                return Ok(bindings);
            }
            self.expect(&Token::Comma)?;
        }
    }

    fn parse_match_arm_pattern(&mut self) -> Result<Option<MatchPattern>, ParseError> {
        let Some(Token::Ident(enum_name)) = self.next().cloned() else {
            return Err(ParseError::new("expected constructor pattern or `_`"));
        };
        if enum_name == "_" {
            return Ok(None);
        }
        self.expect(&Token::ColonColon)?;
        let Some(Token::Ident(ctor_name)) = self.next().cloned() else {
            return Err(ParseError::new(
                "expected constructor name in match pattern",
            ));
        };
        let bindings = if self.tokens.get(self.cursor) == Some(&Token::LParen) {
            self.parse_match_bindings()?
        } else {
            Vec::new()
        };
        Ok(Some(MatchPattern::Constructor {
            enum_name,
            ctor_name,
            bindings,
        }))
    }

    fn parse_match_expr(&mut self) -> Result<Expr, ParseError> {
        let scrutinee = self.parse_expr()?;
        self.expect(&Token::LBrace)?;
        let mut arms = Vec::new();
        let mut default = None;
        loop {
            if self.eat(&Token::RBrace) {
                break;
            }
            let pattern = self.parse_match_arm_pattern()?;
            self.expect(&Token::FatArrow)?;
            let body = self.parse_expr()?;
            match pattern {
                Some(pattern) => arms.push(MatchArm { pattern, body }),
                None => {
                    if default.is_some() {
                        return Err(ParseError::new(
                            "match expression cannot contain multiple `_` arms",
                        ));
                    }
                    default = Some(Box::new(body));
                }
            }
            if self.eat(&Token::Comma) {
                continue;
            }
            self.expect(&Token::RBrace)?;
            break;
        }
        Ok(Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms,
            default,
        })
    }

    fn parse_spec_ty(&mut self) -> Result<SpecTy, ParseError> {
        let Some(Token::Ident(ident)) = self.next().cloned() else {
            return Err(ParseError::new("expected a type argument"));
        };
        let args = if self.eat(&Token::Lt) {
            let mut args = Vec::new();
            if !self.eat(&Token::Gt) {
                loop {
                    args.push(self.parse_spec_ty()?);
                    if self.eat(&Token::Gt) {
                        break;
                    }
                    self.expect(&Token::Comma)?;
                }
            }
            args
        } else {
            Vec::new()
        };
        match ident.as_str() {
            "Int" if args.is_empty() => Ok(SpecTy::Int),
            "RustTy" if args.is_empty() => Ok(SpecTy::RustTy),
            "RustTy" => Err(ParseError::new(format!(
                "spec type `RustTy` expects 0 type arguments, found {}",
                args.len()
            ))),
            "i8" if args.is_empty() => Ok(SpecTy::I8),
            "i16" if args.is_empty() => Ok(SpecTy::I16),
            "i32" if args.is_empty() => Ok(SpecTy::I32),
            "i64" if args.is_empty() => Ok(SpecTy::I64),
            "isize" if args.is_empty() => Ok(SpecTy::Isize),
            "u8" if args.is_empty() => Ok(SpecTy::U8),
            "u16" if args.is_empty() => Ok(SpecTy::U16),
            "u32" if args.is_empty() => Ok(SpecTy::U32),
            "u64" if args.is_empty() => Ok(SpecTy::U64),
            "usize" if args.is_empty() => Ok(SpecTy::Usize),
            "bool" if args.is_empty() => Ok(SpecTy::Bool),
            "Seq" if args.len() == 1 => Ok(SpecTy::Seq(Box::new(args[0].clone()))),
            "Seq" => Err(ParseError::new(format!(
                "spec type `Seq` expects 1 type argument, found {}",
                args.len()
            ))),
            "Ref" if args.len() == 1 => Ok(SpecTy::Ref(Box::new(args[0].clone()))),
            "Ref" => Err(ParseError::new(format!(
                "spec type `Ref` expects 1 type argument, found {}",
                args.len()
            ))),
            "Mut" if args.len() == 1 => Ok(SpecTy::Mut(Box::new(args[0].clone()))),
            "Mut" => Err(ParseError::new(format!(
                "spec type `Mut` expects 1 type argument, found {}",
                args.len()
            ))),
            "Provenance" if args.is_empty() => Ok(provenance_spec_ty()),
            "Provenance" => Err(ParseError::new(format!(
                "spec type `Provenance` expects 0 type arguments, found {}",
                args.len()
            ))),
            "Ptr" if args.is_empty() => Ok(ptr_spec_ty()),
            "Ptr" => Err(ParseError::new(format!(
                "spec type `Ptr` expects 0 type arguments, found {}",
                args.len()
            ))),
            _ if args.is_empty() && self.type_params.iter().any(|param| param == &ident) => {
                Ok(SpecTy::TypeParam(ident))
            }
            _ => Ok(SpecTy::Enum { name: ident, args }),
        }
    }

    fn try_parse_call_type_args(&mut self) -> Result<Option<Vec<SpecTy>>, ParseError> {
        let saved = self.cursor;
        let saw_turbofish = self.eat(&Token::ColonColon);
        if !self.eat(&Token::Lt) {
            self.cursor = saved;
            return Ok(None);
        }
        let mut args = Vec::new();
        if !self.eat(&Token::Gt) {
            loop {
                args.push(self.parse_spec_ty()?);
                if self.eat(&Token::Gt) {
                    break;
                }
                self.expect(&Token::Comma)?;
            }
        }
        match self.tokens.get(self.cursor) {
            Some(Token::LParen) | Some(Token::ColonColon) => Ok(Some(args)),
            _ if saw_turbofish => Err(ParseError::new(
                "expected `(` or `::` after type arguments in spec expression",
            )),
            _ => {
                self.cursor = saved;
                Ok(None)
            }
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match self.next().cloned() {
            Some(Token::Bool(value)) => Ok(Expr::Bool(value)),
            Some(Token::Int(value)) => Ok(Expr::Int(value)),
            Some(Token::Ident(ident)) if ident == "match" => self.parse_match_expr(),
            Some(Token::Ident(ident)) => {
                let type_args = self.try_parse_call_type_args()?.unwrap_or_default();
                if !ident.starts_with("__")
                    && type_args.is_empty()
                    && self.next_tokens_start_struct_literal()
                {
                    self.parse_struct_literal(ident)
                } else if self.eat(&Token::ColonColon) {
                    let Some(Token::Ident(ctor)) = self.next().cloned() else {
                        return Err(ParseError::new("expected constructor name after `::`"));
                    };
                    let func = format!("{ident}::{ctor}");
                    let args = if self.tokens.get(self.cursor) == Some(&Token::LParen) {
                        self.parse_call_args()?
                    } else {
                        Vec::new()
                    };
                    Ok(Expr::Call {
                        func,
                        type_args,
                        args,
                    })
                } else if !ident.starts_with("__")
                    && self.tokens.get(self.cursor) == Some(&Token::LParen)
                {
                    Ok(Expr::Call {
                        func: ident,
                        type_args,
                        args: self.parse_call_args()?,
                    })
                } else {
                    Ok(Expr::Var(ident))
                }
            }
            Some(Token::LParen) => {
                let expr = self.parse_expr()?;
                self.expect(&Token::RParen)?;
                Ok(expr)
            }
            Some(Token::LBrace) => {
                let name = match self.next().cloned() {
                    Some(Token::Ident(name)) => name,
                    _ => {
                        return Err(ParseError::new(
                            "expected a Rust binding name inside `{...}`",
                        ));
                    }
                };
                if name == "type" {
                    let text = self.parse_rust_type_expr_text()?;
                    self.expect(&Token::RBrace)?;
                    return Ok(Expr::RustType(RustTypeExpr { text }));
                }
                if self.tokens.get(self.cursor) != Some(&Token::RBrace) {
                    return Err(ParseError::new(
                        "expected `}` after Rust binding name in `{...}`",
                    ));
                }
                self.expect(&Token::RBrace)?;
                Ok(Expr::Interpolated(name))
            }
            Some(Token::LBracket) => self.parse_seq_literal(),
            _ => Err(ParseError::new("expected a spec expression")),
        }
    }

    fn parse_rust_type_expr_text(&mut self) -> Result<String, ParseError> {
        let ty = self.parse_rust_type_text()?;
        if self.tokens.get(self.cursor) != Some(&Token::RBrace) {
            return Err(ParseError::new(
                "expected `}` after Rust type in `{type ...}`",
            ));
        }
        Ok(ty)
    }

    fn parse_rust_type_text(&mut self) -> Result<String, ParseError> {
        if self.eat(&Token::Amp) {
            let mutability = match self.tokens.get(self.cursor) {
                Some(Token::Ident(ident)) if ident == "mut" => {
                    self.cursor += 1;
                    "mut "
                }
                _ => "",
            };
            let inner = self.parse_rust_type_text()?;
            return Ok(format!("&{mutability}{inner}"));
        }
        if self.eat(&Token::Star) {
            let kind = match self.next().cloned() {
                Some(Token::Ident(kind)) if kind == "const" || kind == "mut" => kind,
                _ => {
                    return Err(ParseError::new(
                        "expected `const` or `mut` after `*` in Rust type",
                    ));
                }
            };
            let inner = self.parse_rust_type_text()?;
            return Ok(format!("*{kind} {inner}"));
        }
        if self.eat(&Token::LParen) {
            if self.eat(&Token::RParen) {
                return Ok("()".to_owned());
            }
            let mut items = Vec::new();
            loop {
                items.push(self.parse_rust_type_text()?);
                if self.eat(&Token::RParen) {
                    break;
                }
                self.expect(&Token::Comma)?;
            }
            return Ok(format!("({})", items.join(", ")));
        }

        let mut text = match self.next().cloned() {
            Some(Token::Ident(ident)) => ident,
            _ => return Err(ParseError::new("expected Rust type after `{type`")),
        };
        while self.eat(&Token::ColonColon) {
            let Some(Token::Ident(segment)) = self.next().cloned() else {
                return Err(ParseError::new(
                    "expected path segment after `::` in Rust type",
                ));
            };
            text.push_str("::");
            text.push_str(&segment);
        }
        if self.eat(&Token::Lt) {
            let mut args = Vec::new();
            if !self.eat(&Token::Gt) {
                loop {
                    args.push(self.parse_rust_type_text()?);
                    if self.eat(&Token::Gt) {
                        break;
                    }
                    self.expect(&Token::Comma)?;
                }
            }
            text.push('<');
            text.push_str(&args.join(", "));
            text.push('>');
        }
        Ok(text)
    }

    fn parse_struct_literal(&mut self, name: String) -> Result<Expr, ParseError> {
        self.expect(&Token::LBrace)?;
        let mut fields = Vec::new();
        if self.eat(&Token::RBrace) {
            return Ok(Expr::StructLit { name, fields });
        }
        loop {
            let Some(Token::Ident(field_name)) = self.next().cloned() else {
                return Err(ParseError::new("expected a field name in struct literal"));
            };
            self.expect(&Token::Colon)?;
            fields.push(StructLitField {
                name: field_name,
                value: self.parse_expr()?,
            });
            if self.eat(&Token::RBrace) {
                return Ok(Expr::StructLit { name, fields });
            }
            self.expect(&Token::Comma)?;
        }
    }

    fn next_tokens_start_struct_literal(&self) -> bool {
        matches!(
            (
                self.tokens.get(self.cursor),
                self.tokens.get(self.cursor + 1),
                self.tokens.get(self.cursor + 2),
            ),
            (
                Some(Token::LBrace),
                Some(Token::Ident(_)),
                Some(Token::Colon)
            ) | (Some(Token::LBrace), Some(Token::RBrace), _)
        )
    }

    fn parse_seq_literal(&mut self) -> Result<Expr, ParseError> {
        let mut items = Vec::new();
        if self.eat(&Token::RBracket) {
            return Ok(Expr::SeqLit(items));
        }
        loop {
            items.push(self.parse_expr()?);
            if self.eat(&Token::RBracket) {
                return Ok(Expr::SeqLit(items));
            }
            self.expect(&Token::Comma)?;
        }
    }

    fn eat(&mut self, token: &Token) -> bool {
        if self.tokens.get(self.cursor) == Some(token) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, token: &Token) -> Result<(), ParseError> {
        if self.eat(token) {
            Ok(())
        } else {
            Err(ParseError::new(format!("expected token {:?}", token)))
        }
    }

    fn next(&mut self) -> Option<&Token> {
        let token = self.tokens.get(self.cursor);
        if token.is_some() {
            self.cursor += 1;
        }
        token
    }
}

#[cfg(test)]
pub fn parse_pure_fn_block(text: &str) -> Result<Vec<PureFnDef>, ParseError> {
    Ok(parse_ghost_block(text)?.pure_fns)
}

pub fn parse_ghost_block(text: &str) -> Result<GhostBlock, ParseError> {
    let mut parser = GhostBlockParser::new(text);
    let mut block = GhostBlock::default();
    while parser.skip_ws() {
        match parser.parse_item()? {
            GhostItem::Enum(def) => block.enums.push(def),
            GhostItem::Struct(def) => block.structs.push(def),
            GhostItem::PureFn(def) => block.pure_fns.push(def),
            GhostItem::Lemma(def) => block.lemmas.push(def),
        }
    }
    Ok(block)
}

enum GhostItem {
    Enum(EnumDef),
    Struct(StructDef),
    PureFn(PureFnDef),
    Lemma(LemmaDef),
}

struct GhostBlockParser<'a> {
    text: &'a str,
    cursor: usize,
}

impl<'a> GhostBlockParser<'a> {
    fn new(text: &'a str) -> Self {
        Self { text, cursor: 0 }
    }

    fn skip_ws(&mut self) -> bool {
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() {
                self.cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        self.cursor < self.text.len()
    }

    fn parse_item(&mut self) -> Result<GhostItem, ParseError> {
        if self.starts_with_keyword("enum") {
            self.expect_keyword("enum")?;
            return Ok(GhostItem::Enum(self.parse_enum_def()?));
        }
        if self.starts_with_keyword("struct") {
            self.expect_keyword("struct")?;
            return Ok(GhostItem::Struct(self.parse_struct_def()?));
        }
        let is_unsafe = if self.starts_with_keyword("unsafe") {
            self.expect_keyword("unsafe")?;
            true
        } else {
            false
        };
        self.expect_keyword("fn")?;
        let name = self.parse_ident()?;
        let type_params = self.parse_type_params()?;
        self.expect_char('(')?;
        let mut params = Vec::new();
        self.skip_ws();
        if !self.eat_char(')') {
            loop {
                let param_name = self.parse_ident()?;
                self.expect_char(':')?;
                let ty = self.parse_spec_ty_annotation(&type_params, &[',', ')'])?;
                params.push(PureFnParam {
                    name: param_name,
                    ty,
                });
                self.skip_ws();
                if self.eat_char(')') {
                    break;
                }
                self.expect_char(',')?;
            }
        }
        self.skip_ws();
        if self.text[self.cursor..].starts_with("->") {
            return Ok(GhostItem::PureFn(self.parse_pure_fn_def(
                name,
                type_params,
                params,
            )?));
        }
        Ok(GhostItem::Lemma(self.parse_lemma_def(
            name,
            is_unsafe,
            type_params,
            params,
        )?))
    }

    fn parse_enum_def(&mut self) -> Result<EnumDef, ParseError> {
        let name = self.parse_ident()?;
        let type_params = self.parse_type_params()?;
        self.expect_char('{')?;
        let mut ctors = Vec::new();
        loop {
            self.skip_ws();
            if self.eat_char('}') {
                break;
            }
            let ctor_name = self.parse_ident()?;
            let mut fields = Vec::new();
            self.skip_ws();
            if self.eat_char('(') {
                self.skip_ws();
                if !self.eat_char(')') {
                    loop {
                        fields.push(self.parse_spec_ty_annotation(&type_params, &[',', ')'])?);
                        self.skip_ws();
                        if self.eat_char(')') {
                            break;
                        }
                        self.expect_char(',')?;
                    }
                }
            }
            ctors.push(EnumCtorDef {
                name: ctor_name,
                fields,
            });
            self.skip_ws();
            if self.eat_char(',') {
                continue;
            }
            self.expect_char('}')?;
            break;
        }
        Ok(EnumDef {
            name,
            type_params,
            ctors,
        })
    }

    fn parse_struct_def(&mut self) -> Result<StructDef, ParseError> {
        let name = self.parse_ident()?;
        let type_params = self.parse_type_params()?;
        self.expect_char('{')?;
        let mut fields = Vec::new();
        loop {
            self.skip_ws();
            if self.eat_char('}') {
                break;
            }
            let field_name = self.parse_ident()?;
            self.expect_char(':')?;
            let ty = self.parse_spec_ty_annotation(&type_params, &[',', '}'])?;
            fields.push(StructFieldTy {
                name: field_name,
                ty,
            });
            self.skip_ws();
            if self.eat_char(',') {
                continue;
            }
            self.expect_char('}')?;
            break;
        }
        Ok(StructDef {
            name,
            type_params,
            fields,
        })
    }

    fn parse_pure_fn_def(
        &mut self,
        name: String,
        type_params: Vec<String>,
        params: Vec<PureFnParam>,
    ) -> Result<PureFnDef, ParseError> {
        self.expect_arrow()?;
        let result_ty = self.parse_spec_ty_annotation(&type_params, &['{'])?;
        self.expect_char('{')?;
        let body = self.parse_braced_body()?;
        Ok(PureFnDef {
            name,
            type_params: type_params.clone(),
            params,
            result_ty,
            body: parse_raw_expr_with_type_params("pure function body", body.trim(), &type_params)?,
        })
    }

    fn parse_lemma_def(
        &mut self,
        name: String,
        is_unsafe: bool,
        type_params: Vec<String>,
        params: Vec<PureFnParam>,
    ) -> Result<LemmaDef, ParseError> {
        let mut req = None;
        let mut resource_reqs = Vec::new();
        let mut ens = None;
        let mut resource_ens = Vec::new();
        loop {
            self.skip_ws();
            if self.peek_char() == Some('{') {
                break;
            }
            if self.starts_with_keyword("resource") {
                self.expect_keyword("resource")?;
                self.skip_ws();
                if self.starts_with_keyword("req") {
                    self.expect_keyword("req")?;
                    resource_reqs.push(self.parse_line_resource_assertion("lemma resource req")?);
                    continue;
                }
                self.expect_keyword("ens")?;
                resource_ens.push(self.parse_line_resource_assertion("lemma resource ens")?);
                continue;
            }
            if self.starts_with_keyword("req") {
                if req.is_some() {
                    return Err(ParseError::new("multiple lemma req clauses"));
                }
                self.expect_keyword("req")?;
                req = Some(self.parse_line_expr("lemma req", &type_params)?);
                continue;
            }
            if self.starts_with_keyword("ens") {
                if ens.is_some() {
                    return Err(ParseError::new("multiple lemma ens clauses"));
                }
                self.expect_keyword("ens")?;
                ens = Some(self.parse_line_expr("lemma ens", &type_params)?);
                continue;
            }
            return Err(ParseError::new("expected lemma contract clause"));
        }
        self.expect_char('{')?;
        let body = self.parse_braced_body()?;
        let body = self.parse_lemma_body(body, &type_params)?;
        Ok(LemmaDef {
            name,
            is_unsafe,
            type_params,
            params,
            req: req.unwrap_or(Expr::Bool(true)),
            resource_reqs,
            ens: ens.unwrap_or(Expr::Bool(true)),
            resource_ens,
            body,
        })
    }

    fn parse_type_params(&mut self) -> Result<Vec<String>, ParseError> {
        self.skip_ws();
        if !self.eat_char('<') {
            return Ok(Vec::new());
        }
        let mut type_params = Vec::new();
        loop {
            type_params.push(self.parse_ident()?);
            self.skip_ws();
            if self.eat_char('>') {
                return Ok(type_params);
            }
            self.expect_char(',')?;
        }
    }

    fn parse_braced_body(&mut self) -> Result<&'a str, ParseError> {
        let body_start = self.cursor;
        let mut depth = 1usize;
        while let Some(ch) = self.peek_char() {
            self.cursor += ch.len_utf8();
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        let end = self.cursor - 1;
                        return Ok(&self.text[body_start..end]);
                    }
                }
                _ => {}
            }
        }
        Err(ParseError::new("unclosed `{` in pure function block"))
    }

    fn parse_lemma_body(
        &self,
        body: &'a str,
        type_params: &[String],
    ) -> Result<Vec<GhostStmt>, ParseError> {
        let mut parser = Self::new(body);
        parser.parse_lemma_stmts(type_params)
    }

    fn parse_lemma_stmts(&mut self, type_params: &[String]) -> Result<Vec<GhostStmt>, ParseError> {
        let mut stmts = Vec::new();
        while self.skip_ws() {
            stmts.push(self.parse_lemma_stmt(type_params)?);
        }
        Ok(stmts)
    }

    fn parse_lemma_stmt(&mut self, type_params: &[String]) -> Result<GhostStmt, ParseError> {
        if self.starts_with_keyword("assert") {
            self.expect_keyword("assert")?;
            let (expr_text, next) = self.parse_stmt_expr_text(self.text, self.cursor)?;
            self.cursor = next;
            return Ok(GhostStmt::Assert(parse_source_expr_with_type_params(
                "lemma assert",
                expr_text,
                type_params,
            )?));
        }
        if self.starts_with_keyword("assume") {
            self.expect_keyword("assume")?;
            let (expr_text, next) = self.parse_stmt_expr_text(self.text, self.cursor)?;
            self.cursor = next;
            return Ok(GhostStmt::Assume(parse_source_expr_with_type_params(
                "lemma assume",
                expr_text,
                type_params,
            )?));
        }
        if self.starts_with_keyword("match") {
            self.expect_keyword("match")?;
            return self.parse_lemma_match_stmt(type_params);
        }
        let (expr_text, next) = self.parse_stmt_expr_text(self.text, self.cursor)?;
        self.cursor = next;
        match parse_source_expr_with_type_params("lemma call", expr_text, type_params)? {
            Expr::Call {
                func,
                type_args,
                args,
            } => Ok(GhostStmt::Call {
                name: func,
                type_args,
                args,
            }),
            _ => Err(ParseError::new(
                "lemma call must be of the form `name(args...)`",
            )),
        }
    }

    fn parse_lemma_match_stmt(&mut self, type_params: &[String]) -> Result<GhostStmt, ParseError> {
        let (scrutinee_text, cursor) = self.parse_until_top_level_char('{')?;
        self.cursor = cursor;
        let scrutinee = parse_source_expr_with_type_params(
            "lemma match scrutinee",
            scrutinee_text,
            type_params,
        )?;
        self.expect_char('{')?;
        let mut arms = Vec::new();
        let mut default = None;
        let mut seen_default = false;
        loop {
            self.skip_ws();
            if self.eat_char('}') {
                break;
            }
            if seen_default {
                return Err(ParseError::new("default match arm must be last"));
            }
            let (pattern_text, next) = self.parse_until_top_level_fat_arrow()?;
            self.cursor = next;
            self.expect_char('{')?;
            let body_text = self.parse_braced_body()?;
            let body = self.parse_lemma_body(body_text, type_params)?;
            let pattern_text = pattern_text.trim();
            if pattern_text == "_" {
                if default.is_some() {
                    return Err(ParseError::new("duplicate default match arm"));
                }
                default = Some(body);
                seen_default = true;
            } else {
                arms.push(GhostMatchArm {
                    pattern: parse_raw_match_pattern(pattern_text)?,
                    body,
                });
            }
            self.skip_ws();
            if self.eat_char(',') {
                continue;
            }
            if self.eat_char('}') {
                break;
            }
            if matches!(self.peek_char(), Some(ch) if ch == '_' || ch.is_ascii_alphabetic()) {
                continue;
            }
            return Err(ParseError::new("expected `,` or `}` after match arm"));
        }
        Ok(GhostStmt::Match {
            scrutinee,
            arms,
            default,
        })
    }

    fn parse_line_expr(&mut self, kind: &str, type_params: &[String]) -> Result<Expr, ParseError> {
        let (text, next) = self.parse_line_expr_text(self.text, self.cursor)?;
        self.cursor = next;
        parse_source_expr_with_type_params(kind, text, type_params)
    }

    fn parse_line_resource_assertion(
        &mut self,
        kind: &str,
    ) -> Result<ResourceAssertion, ParseError> {
        let (text, next) = self.parse_line_expr_text(self.text, self.cursor)?;
        self.cursor = next;
        parse_resource_assertion(text)
            .map_err(|err| ParseError::new(err.to_string().replace("//@ resource assert", kind)))
    }

    fn parse_spec_ty_annotation(
        &mut self,
        type_params: &[String],
        terminators: &[char],
    ) -> Result<SpecTy, ParseError> {
        let (text, next) = self.capture_until_top_level_char(terminators)?;
        self.cursor = next;
        parse_spec_ty_text_with_params(text, type_params)
    }

    fn parse_line_expr_text(
        &self,
        text: &'a str,
        mut cursor: usize,
    ) -> Result<(&'a str, usize), ParseError> {
        while let Some(ch) = text[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        let start = cursor;
        while let Some(ch) = text[cursor..].chars().next() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            cursor += ch.len_utf8();
        }
        let expr = text[start..cursor].trim_end();
        if expr.is_empty() {
            return Err(ParseError::new("expected spec expression"));
        }
        Ok((expr, cursor))
    }

    fn parse_stmt_expr_text(
        &self,
        text: &'a str,
        mut cursor: usize,
    ) -> Result<(&'a str, usize), ParseError> {
        while let Some(ch) = text[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        let start = cursor;
        while let Some(ch) = text[cursor..].chars().next() {
            if ch == ';' {
                let expr = text[start..cursor].trim_end();
                if expr.is_empty() {
                    return Err(ParseError::new("expected spec expression"));
                }
                return Ok((expr, cursor + 1));
            }
            cursor += ch.len_utf8();
        }
        Err(ParseError::new("expected `;` after ghost statement"))
    }

    fn capture_until_top_level_char(
        &self,
        terminators: &[char],
    ) -> Result<(&'a str, usize), ParseError> {
        let mut cursor = self.cursor;
        while let Some(ch) = self.text[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        let start = cursor;
        let mut depth = 0usize;
        while cursor < self.text.len() {
            let ch = self.text[cursor..].chars().next().expect("char");
            match ch {
                _ if depth == 0 && terminators.contains(&ch) => {
                    let text = self.text[start..cursor].trim_end();
                    if text.is_empty() {
                        return Err(ParseError::new("expected spec type"));
                    }
                    return Ok((text, cursor));
                }
                '(' | '[' | '<' => depth += 1,
                ')' | ']' | '>' => depth = depth.saturating_sub(1),
                _ => {}
            }
            cursor += ch.len_utf8();
        }
        Err(ParseError::new("expected spec type"))
    }

    fn parse_until_top_level_char(&self, target: char) -> Result<(&'a str, usize), ParseError> {
        let start = self.cursor;
        let mut cursor = self.cursor;
        let mut depth = 0usize;
        while cursor < self.text.len() {
            let ch = self.text[cursor..].chars().next().expect("char");
            match ch {
                '(' | '[' | '<' => depth += 1,
                ')' | ']' | '>' => depth = depth.saturating_sub(1),
                _ if ch == target && depth == 0 => {
                    let text = self.text[start..cursor].trim_end();
                    if text.is_empty() {
                        return Err(ParseError::new("expected spec expression"));
                    }
                    return Ok((text, cursor));
                }
                _ => {}
            }
            cursor += ch.len_utf8();
        }
        Err(ParseError::new(format!(
            "expected `{target}` in lemma match"
        )))
    }

    fn parse_until_top_level_fat_arrow(&self) -> Result<(&'a str, usize), ParseError> {
        let start = self.cursor;
        let mut cursor = self.cursor;
        let mut depth = 0usize;
        while cursor < self.text.len() {
            let ch = self.text[cursor..].chars().next().expect("char");
            match ch {
                '(' | '[' | '<' => depth += 1,
                ')' | ']' | '>' => depth = depth.saturating_sub(1),
                '=' if depth == 0 && self.text[cursor..].starts_with("=>") => {
                    let text = self.text[start..cursor].trim_end();
                    if text.is_empty() {
                        return Err(ParseError::new("expected match arm pattern"));
                    }
                    return Ok((text, cursor + 2));
                }
                _ => {}
            }
            cursor += ch.len_utf8();
        }
        Err(ParseError::new("expected `=>` in lemma match arm"))
    }

    fn parse_ident(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        let start = self.cursor;
        let mut chars = self.text[self.cursor..].chars();
        let Some(first) = chars.next() else {
            return Err(ParseError::new("unexpected end of pure function block"));
        };
        if !(first.is_ascii_alphabetic() || first == '_') {
            return Err(ParseError::new(
                "expected identifier in pure function block",
            ));
        }
        self.cursor += first.len_utf8();
        while let Some(ch) = self.peek_char() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                self.cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        Ok(self.text[start..self.cursor].to_owned())
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<(), ParseError> {
        self.skip_ws();
        if self.starts_with_keyword(keyword) {
            self.cursor += keyword.len();
            Ok(())
        } else {
            Err(ParseError::new(format!(
                "expected keyword `{keyword}` in pure function block"
            )))
        }
    }

    fn expect_arrow(&mut self) -> Result<(), ParseError> {
        self.skip_ws();
        if self.text[self.cursor..].starts_with("->") {
            self.cursor += 2;
            Ok(())
        } else {
            Err(ParseError::new("expected `->` in pure function block"))
        }
    }

    fn expect_char(&mut self, ch: char) -> Result<(), ParseError> {
        self.skip_ws();
        if self.eat_char(ch) {
            Ok(())
        } else {
            Err(ParseError::new(format!(
                "expected `{ch}` in pure function block"
            )))
        }
    }

    fn eat_char(&mut self, ch: char) -> bool {
        if self.peek_char() == Some(ch) {
            self.cursor += ch.len_utf8();
            true
        } else {
            false
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.text[self.cursor..].chars().next()
    }

    fn starts_with_keyword(&self, keyword: &str) -> bool {
        let Some(rest) = self.text.get(self.cursor..) else {
            return false;
        };
        let Some(suffix) = rest.strip_prefix(keyword) else {
            return false;
        };
        suffix
            .chars()
            .next()
            .is_none_or(|ch| !(ch.is_ascii_alphanumeric() || ch == '_'))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        parse_expr, parse_ghost_block, parse_pure_fn_block, parse_raw_expr,
        parse_spec_ty_text_with_params,
    };
    use crate::spec::{
        BinaryOp, EnumCtorDef, EnumDef, Expr, GhostBlock, GhostStmt, IntLiteral, IntSuffix,
        LemmaDef, MatchArm, MatchBinding, MatchPattern, PureFnDef, PureFnParam, RustTypeExpr,
        SpecTy, StructDef, StructFieldTy, UnaryOp,
    };

    fn true_expr() -> Expr {
        Expr::Bool(true)
    }

    #[test]
    fn parses_deref_and_fin() {
        let expr = parse_expr("assert", r#"*{x} == {y}.fin"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Deref {
                    base: Box::new(Expr::Interpolated("x".to_owned())),
                }),
                rhs: Box::new(Expr::Field {
                    base: Box::new(Expr::Interpolated("y".to_owned())),
                    name: "fin".to_owned(),
                }),
            }
        );
    }

    #[test]
    fn parses_tuple_projection() {
        let expr = parse_expr("assert", r#"{x}.0 == 1i32"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::TupleField {
                    base: Box::new(Expr::Interpolated("x".to_owned())),
                    index: 0,
                }),
                rhs: Box::new(Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(IntSuffix::I32),
                })),
            }
        );
    }

    #[test]
    fn rejects_question_binding_syntax() {
        let expr = parse_expr("assert", r#"?x == 3"#);
        assert!(expr.is_err(), "{expr:?}");
    }

    #[test]
    fn keeps_operator_precedence() {
        let expr = parse_expr("assert", r#"!false || 1 + 2 * 3 == 7"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Or,
                lhs: Box::new(Expr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(Expr::Bool(false)),
                }),
                rhs: Box::new(Expr::Binary {
                    op: BinaryOp::Eq,
                    lhs: Box::new(Expr::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(Expr::Int(IntLiteral {
                            digits: "1".to_owned(),
                            suffix: None,
                        })),
                        rhs: Box::new(Expr::Binary {
                            op: BinaryOp::Mul,
                            lhs: Box::new(Expr::Int(IntLiteral {
                                digits: "2".to_owned(),
                                suffix: None,
                            })),
                            rhs: Box::new(Expr::Int(IntLiteral {
                                digits: "3".to_owned(),
                                suffix: None,
                            })),
                        }),
                    }),
                    rhs: Box::new(Expr::Int(IntLiteral {
                        digits: "7".to_owned(),
                        suffix: None,
                    })),
                }),
            }
        );
    }

    #[test]
    fn parses_named_field_accessor() {
        let expr = parse_expr("assert", r#"{x}.left == 1i32"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Field {
                    base: Box::new(Expr::Interpolated("x".to_owned())),
                    name: "left".to_owned(),
                }),
                rhs: Box::new(Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(IntSuffix::I32),
                })),
            }
        );
    }

    #[test]
    fn parses_large_integer_suffixes() {
        let expr = parse_expr("assert", r#"18446744073709551615u64 == 0usize"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Int(IntLiteral {
                    digits: "18446744073709551615".to_owned(),
                    suffix: Some(IntSuffix::U64),
                })),
                rhs: Box::new(Expr::Int(IntLiteral {
                    digits: "0".to_owned(),
                    suffix: Some(IntSuffix::Usize),
                })),
            }
        );
    }

    #[test]
    fn parses_function_call_expression() {
        let expr = parse_expr("assert", r#"seq_rev({xs}) == {ys}"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Call {
                    func: "seq_rev".to_owned(),
                    type_args: vec![],
                    args: vec![Expr::Interpolated("xs".to_owned())],
                }),
                rhs: Box::new(Expr::Interpolated("ys".to_owned())),
            }
        );
    }

    #[test]
    fn parses_enum_constructor_expression() {
        let expr = parse_expr("assert", r#"IntList::Cons(1i32, IntList::Nil)"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Call {
                func: "IntList::Cons".to_owned(),
                type_args: vec![],
                args: vec![
                    Expr::Int(IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(IntSuffix::I32),
                    }),
                    Expr::Call {
                        func: "IntList::Nil".to_owned(),
                        type_args: vec![],
                        args: vec![],
                    },
                ],
            }
        );
    }

    #[test]
    fn parses_generic_enum_constructor_expression() {
        let expr = parse_expr("assert", r#"List::<i32>::Cons(1i32, List::<i32>::Nil)"#);
        assert!(expr.is_ok(), "{expr:?}");
    }

    #[test]
    fn parses_match_expression() {
        let expr = parse_raw_expr(
            "pure function body",
            r#"match xs { List::Nil => 0i32, List::Cons(_, xs0) => len(xs0) }"#,
        )
        .expect("match expr");
        assert_eq!(
            expr,
            Expr::Match {
                scrutinee: Box::new(Expr::Var("xs".to_owned())),
                arms: vec![
                    MatchArm {
                        pattern: MatchPattern::Constructor {
                            enum_name: "List".to_owned(),
                            ctor_name: "Nil".to_owned(),
                            bindings: vec![],
                        },
                        body: Expr::Int(IntLiteral {
                            digits: "0".to_owned(),
                            suffix: Some(IntSuffix::I32),
                        }),
                    },
                    MatchArm {
                        pattern: MatchPattern::Constructor {
                            enum_name: "List".to_owned(),
                            ctor_name: "Cons".to_owned(),
                            bindings: vec![
                                MatchBinding::Wildcard,
                                MatchBinding::Var("xs0".to_owned()),
                            ],
                        },
                        body: Expr::Call {
                            func: "len".to_owned(),
                            type_args: vec![],
                            args: vec![Expr::Var("xs0".to_owned())],
                        },
                    },
                ],
                default: None,
            }
        );
    }

    #[test]
    fn parses_sequence_literal_expression() {
        let expr = parse_raw_expr("assert", r#"[1i32, 2i32]"#).expect("seq literal");
        assert_eq!(
            expr,
            Expr::SeqLit(vec![
                Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(IntSuffix::I32),
                }),
                Expr::Int(IntLiteral {
                    digits: "2".to_owned(),
                    suffix: Some(IntSuffix::I32),
                }),
            ])
        );
    }

    #[test]
    fn parses_sequence_concat_expression() {
        let expr = parse_raw_expr("assert", r#"[1i32] ++ xs"#).expect("seq concat");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Concat,
                lhs: Box::new(Expr::SeqLit(vec![Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(IntSuffix::I32),
                })])),
                rhs: Box::new(Expr::Var("xs".to_owned())),
            }
        );
    }

    #[test]
    fn parses_sequence_index_expression() {
        let expr = parse_raw_expr("assert", r#"xs[Nat::Zero]"#).expect("seq index");
        assert_eq!(
            expr,
            Expr::Index {
                base: Box::new(Expr::Var("xs".to_owned())),
                index: Box::new(Expr::Call {
                    func: "Nat::Zero".to_owned(),
                    type_args: vec![],
                    args: vec![],
                }),
            }
        );
    }

    #[test]
    fn parses_rust_type_expression() {
        let expr = parse_raw_expr("assert", r#"{type *const T}"#).expect("rust type");
        assert_eq!(
            expr,
            Expr::RustType(RustTypeExpr {
                text: "*const T".to_owned(),
            })
        );
    }

    #[test]
    fn parses_spec_type_text_with_type_params() {
        let ty =
            parse_spec_ty_text_with_params("Seq<T>", &["T".to_owned()]).expect("generic spec type");
        assert_eq!(ty, SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))));

        let ty = parse_spec_ty_text_with_params("List<i32>", &[]).expect("named generic spec type");
        assert_eq!(
            ty,
            SpecTy::Enum {
                name: "List".to_owned(),
                args: vec![SpecTy::I32],
            }
        );
    }

    #[test]
    fn parses_statement_expression_with_trailing_semicolon() {
        let expr = super::parse_statement_expr("assert", r#"{x} == 1i32;"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Interpolated("x".to_owned())),
                rhs: Box::new(Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(IntSuffix::I32),
                })),
            }
        );
    }

    #[test]
    fn keeps_bare_and_interpolated_names_distinct() {
        let expr = parse_expr("assert", r#"x == {x}"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Var("x".to_owned())),
                rhs: Box::new(Expr::Interpolated("x".to_owned())),
            }
        );
    }

    #[test]
    fn rejects_non_binding_interpolation() {
        let err = parse_expr("assert", r#"{x + 1i32} == 2i32"#).expect_err("parse should fail");
        assert_eq!(
            err.message,
            "expected `}` after Rust binding name in `{...}`"
        );
    }

    #[test]
    fn rejects_legacy_string_literal_statement_expression() {
        let err = super::parse_statement_expr("assert", r#""{x} == 1i32";"#)
            .expect_err("legacy string literal form should be rejected");
        assert!(
            err.to_string().contains("expected a spec expression")
                || err
                    .to_string()
                    .contains("unexpected character `\"` in spec expression"),
            "{err}"
        );
    }

    #[test]
    fn parses_pure_function_block() {
        let defs = parse_pure_fn_block(
            r#"
fn add1(x: i32) -> i32 {
    x + 1i32
}
"#,
        )
        .expect("pure fn block");
        assert_eq!(
            defs,
            vec![PureFnDef {
                name: "add1".to_owned(),
                type_params: vec![],
                params: vec![PureFnParam {
                    name: "x".to_owned(),
                    ty: SpecTy::I32,
                }],
                result_ty: SpecTy::I32,
                body: Expr::Binary {
                    op: BinaryOp::Add,
                    lhs: Box::new(Expr::Var("x".to_owned())),
                    rhs: Box::new(Expr::Int(IntLiteral {
                        digits: "1".to_owned(),
                        suffix: Some(IntSuffix::I32),
                    })),
                },
            }]
        );
    }

    #[test]
    fn parses_generic_seq_types_in_pure_function_block() {
        let defs = parse_pure_fn_block(
            r#"
fn is_rev(x: Seq<i32>) -> bool {
    true
}
"#,
        )
        .expect("generic sequence type should parse");
        assert_eq!(defs[0].params[0].ty, SpecTy::Seq(Box::new(SpecTy::I32)));
        assert_eq!(defs[0].result_ty, SpecTy::Bool);
    }

    #[test]
    fn parses_true_false_literals() {
        assert_eq!(parse_expr("assert", "true").unwrap(), Expr::Bool(true));
        assert_eq!(parse_expr("assert", "false").unwrap(), Expr::Bool(false));
    }

    #[test]
    fn parses_nat_integer_suffix() {
        let expr = parse_expr("assert", "43Nat").expect("Nat literal");
        assert_eq!(
            expr,
            Expr::Int(IntLiteral {
                digits: "43".to_owned(),
                suffix: Some(IntSuffix::Nat),
            })
        );
    }

    #[test]
    fn parses_struct_defs_and_literals() {
        let block = parse_ghost_block(
            r#"
struct Foo {
    bar: isize,
    baz: bool,
}
"#,
        )
        .expect("struct block");
        assert_eq!(
            block.structs,
            vec![StructDef {
                name: "Foo".to_owned(),
                type_params: vec![],
                fields: vec![
                    StructFieldTy {
                        name: "bar".to_owned(),
                        ty: SpecTy::Isize,
                    },
                    StructFieldTy {
                        name: "baz".to_owned(),
                        ty: SpecTy::Bool,
                    },
                ],
            }]
        );

        let expr = parse_expr("assert", "Foo { bar: 42isize, baz: true }.bar")
            .expect("struct literal field");
        assert!(matches!(expr, Expr::Field { .. }));
    }

    #[test]
    fn parses_generic_pure_function_definition() {
        let block = parse_ghost_block(
            r#"
fn id<T>(xs: Seq<T>) -> Seq<T> {
    xs
}
"#,
        )
        .expect("generic pure function should parse");
        assert_eq!(block.pure_fns.len(), 1);
        assert_eq!(block.pure_fns[0].name, "id");
        assert_eq!(block.pure_fns[0].type_params, vec!["T".to_owned()]);
        assert_eq!(
            block.pure_fns[0].params[0].ty,
            SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned())))
        );
        assert_eq!(
            block.pure_fns[0].result_ty,
            SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned())))
        );
    }

    #[test]
    fn parses_lemma_block() {
        let block = parse_ghost_block(
            r#"
fn add1(x: i32) -> i32 {
    x + 1i32
}

fn add1_done(x: i32)
  req true
  ens add1(x) == x + 1i32
{
    assert add1(x) == x + 1i32;
}
"#,
        )
        .expect("ghost block");
        assert_eq!(
            block,
            GhostBlock {
                enums: vec![],
                structs: vec![],
                pure_fns: vec![PureFnDef {
                    name: "add1".to_owned(),
                    type_params: vec![],
                    params: vec![PureFnParam {
                        name: "x".to_owned(),
                        ty: SpecTy::I32,
                    }],
                    result_ty: SpecTy::I32,
                    body: Expr::Binary {
                        op: BinaryOp::Add,
                        lhs: Box::new(Expr::Var("x".to_owned())),
                        rhs: Box::new(Expr::Int(IntLiteral {
                            digits: "1".to_owned(),
                            suffix: Some(IntSuffix::I32),
                        })),
                    },
                }],
                lemmas: vec![LemmaDef {
                    name: "add1_done".to_owned(),
                    is_unsafe: false,
                    type_params: vec![],
                    params: vec![PureFnParam {
                        name: "x".to_owned(),
                        ty: SpecTy::I32,
                    }],
                    req: true_expr(),
                    resource_reqs: vec![],
                    ens: Expr::Binary {
                        op: BinaryOp::Eq,
                        lhs: Box::new(Expr::Call {
                            func: "add1".to_owned(),
                            type_args: vec![],
                            args: vec![Expr::Var("x".to_owned())],
                        }),
                        rhs: Box::new(Expr::Binary {
                            op: BinaryOp::Add,
                            lhs: Box::new(Expr::Var("x".to_owned())),
                            rhs: Box::new(Expr::Int(IntLiteral {
                                digits: "1".to_owned(),
                                suffix: Some(IntSuffix::I32),
                            })),
                        }),
                    },
                    resource_ens: vec![],
                    body: vec![GhostStmt::Assert(Expr::Binary {
                        op: BinaryOp::Eq,
                        lhs: Box::new(Expr::Call {
                            func: "add1".to_owned(),
                            type_args: vec![],
                            args: vec![Expr::Var("x".to_owned())],
                        }),
                        rhs: Box::new(Expr::Binary {
                            op: BinaryOp::Add,
                            lhs: Box::new(Expr::Var("x".to_owned())),
                            rhs: Box::new(Expr::Int(IntLiteral {
                                digits: "1".to_owned(),
                                suffix: Some(IntSuffix::I32),
                            })),
                        }),
                    })],
                }],
            }
        );
    }

    #[test]
    fn parses_lemma_match_statement() {
        let block = parse_ghost_block(
            r#"
enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn check(xs: List<i32>)
  req true
  ens true
{
    match xs {
        List::Nil => {
            assert true;
        }
        List::Cons(_, xs0) => {
            check(xs0);
        }
    }
}
"#,
        );
        assert!(block.is_ok(), "{block:?}");
    }

    #[test]
    fn parses_generic_lemma_definition_and_call() {
        let block = parse_ghost_block(
            r#"
fn refl<T>(xs: Seq<T>)
  req true
  ens true
{
    refl::<T>(xs);
}
"#,
        )
        .expect("generic lemma should parse");
        assert_eq!(
            block.lemmas,
            vec![LemmaDef {
                name: "refl".to_owned(),
                is_unsafe: false,
                type_params: vec!["T".to_owned()],
                params: vec![PureFnParam {
                    name: "xs".to_owned(),
                    ty: SpecTy::Seq(Box::new(SpecTy::TypeParam("T".to_owned()))),
                }],
                req: true_expr(),
                resource_reqs: vec![],
                ens: true_expr(),
                resource_ens: vec![],
                body: vec![GhostStmt::Call {
                    name: "refl".to_owned(),
                    type_args: vec![SpecTy::TypeParam("T".to_owned())],
                    args: vec![Expr::Var("xs".to_owned())],
                }],
            }]
        );
    }

    #[test]
    fn parses_unsafe_lemma_resource_contracts() {
        let block = parse_ghost_block(
            r#"
unsafe fn preserves_cell(p: Ptr)
  resource req PointsTo(p.addr, {type i32}, Option::Some(?old)) where old == 0i32
  resource ens PointsTo(p.addr, {type i32}, Option::Some(?new)) where new == old
  req true
  ens true
{
    assert true;
}
"#,
        )
        .expect("unsafe lemma resource contract should parse");

        assert_eq!(block.lemmas.len(), 1);
        assert_eq!(block.lemmas[0].resource_reqs.len(), 1);
        assert_eq!(block.lemmas[0].resource_ens.len(), 1);
    }

    #[test]
    fn parses_pure_function_call_with_explicit_type_args() {
        let expr =
            parse_expr("assert", "seq_rev::<i32>(xs)").expect("explicit pure call should parse");
        assert_eq!(
            expr,
            Expr::Call {
                func: "seq_rev".to_owned(),
                type_args: vec![SpecTy::I32],
                args: vec![Expr::Var("xs".to_owned())],
            }
        );
    }

    #[test]
    fn parses_enum_definitions_in_ghost_block() {
        let block = parse_ghost_block(
            r#"
enum IntList {
    Nil,
    Cons(i32, IntList),
}

fn singleton(x: i32) -> IntList {
    IntList::Cons(x, IntList::Nil)
}
"#,
        )
        .expect("ghost block");
        assert_eq!(
            block,
            GhostBlock {
                enums: vec![EnumDef {
                    name: "IntList".to_owned(),
                    type_params: vec![],
                    ctors: vec![
                        EnumCtorDef {
                            name: "Nil".to_owned(),
                            fields: vec![],
                        },
                        EnumCtorDef {
                            name: "Cons".to_owned(),
                            fields: vec![
                                SpecTy::I32,
                                SpecTy::Enum {
                                    name: "IntList".to_owned(),
                                    args: vec![],
                                },
                            ],
                        },
                    ],
                }],
                structs: vec![],
                pure_fns: vec![PureFnDef {
                    name: "singleton".to_owned(),
                    type_params: vec![],
                    params: vec![PureFnParam {
                        name: "x".to_owned(),
                        ty: SpecTy::I32,
                    }],
                    result_ty: SpecTy::Enum {
                        name: "IntList".to_owned(),
                        args: vec![],
                    },
                    body: Expr::Call {
                        func: "IntList::Cons".to_owned(),
                        type_args: vec![],
                        args: vec![
                            Expr::Var("x".to_owned()),
                            Expr::Call {
                                func: "IntList::Nil".to_owned(),
                                type_args: vec![],
                                args: vec![],
                            },
                        ],
                    },
                }],
                lemmas: vec![],
            }
        );
    }

    #[test]
    fn parses_generic_enum_definitions_in_ghost_block() {
        let block = parse_ghost_block(
            r#"
enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn singleton(x: i32) -> List<i32> {
    List::Cons(x, List::Nil)
}
"#,
        );
        assert!(block.is_ok(), "{block:?}");
    }

    #[test]
    fn parses_recursive_pure_function_with_match_body() {
        let block = parse_ghost_block(
            r#"
enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn len(xs: List<i32>) -> i32 {
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
    }
}
"#,
        );
        assert!(block.is_ok(), "{block:?}");
    }

    #[test]
    fn parses_line_comment_style_lemma_items() {
        let source = r#"
//@ fn line_comment_lemma(n: Nat)
//@   req true
//@   ens true
//@ {}

/*@ fn mixed_comment_lemma(n: Nat) */
//@   req true
/*@   ens true */
//@ {}
"#;
        let comments = super::collect_spec_comments(source);
        let block = super::spec_comment_group_text(&comments);
        let parsed = parse_ghost_block(&block);
        assert!(parsed.is_ok(), "{block}\n{parsed:?}");
    }
}

#[cfg(test)]
mod directive_tests {
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
