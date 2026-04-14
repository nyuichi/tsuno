#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Bool(bool),
    Int(IntLiteral),
    Var(String),
    Bind(String),
    Call {
        func: String,
        args: Vec<Expr>,
    },
    Field {
        base: Box<Expr>,
        name: String,
    },
    TupleField {
        base: Box<Expr>,
        index: usize,
    },
    Deref {
        base: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        arg: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedExpr {
    pub ty: SpecTy,
    pub kind: TypedExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedExprKind {
    Bool(bool),
    Int(IntLiteral),
    Var(String),
    Bind(String),
    PureCall {
        func: String,
        args: Vec<TypedExpr>,
    },
    BuiltinCall {
        func: BuiltinFn,
        args: Vec<TypedExpr>,
    },
    Field {
        base: Box<TypedExpr>,
        name: String,
        index: usize,
    },
    TupleField {
        base: Box<TypedExpr>,
        index: usize,
    },
    Deref {
        base: Box<TypedExpr>,
    },
    Fin {
        base: Box<TypedExpr>,
    },
    Unary {
        op: UnaryOp,
        arg: Box<TypedExpr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<TypedExpr>,
        rhs: Box<TypedExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntSuffix {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
}

impl IntSuffix {
    pub fn spec_ty(self) -> SpecTy {
        match self {
            Self::I8 => SpecTy::I8,
            Self::I16 => SpecTy::I16,
            Self::I32 => SpecTy::I32,
            Self::I64 => SpecTy::I64,
            Self::Isize => SpecTy::Isize,
            Self::U8 => SpecTy::U8,
            Self::U16 => SpecTy::U16,
            Self::U32 => SpecTy::U32,
            Self::U64 => SpecTy::U64,
            Self::Usize => SpecTy::Usize,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntLiteral {
    pub digits: String,
    pub suffix: Option<IntSuffix>,
}

impl IntLiteral {
    pub fn spec_ty(&self) -> SpecTy {
        self.suffix
            .map(IntSuffix::spec_ty)
            .unwrap_or(SpecTy::IntLiteral)
    }

    fn as_unsuffixed_usize(&self) -> Option<usize> {
        match self.suffix {
            Some(_) => None,
            None => self.digits.parse::<usize>().ok(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecTy {
    Bool,
    IntLiteral,
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    Seq(Box<SpecTy>),
    Tuple(Vec<SpecTy>),
    Struct(StructTy),
    Ref(Box<SpecTy>),
    Mut(Box<SpecTy>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BuiltinFn {
    SeqConcat,
    SeqExtract,
    SeqLen,
    SeqNth,
    SeqRev,
    SeqUnit,
}

impl BuiltinFn {
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "seq_concat" => Some(Self::SeqConcat),
            "seq_extract" => Some(Self::SeqExtract),
            "seq_len" => Some(Self::SeqLen),
            "seq_nth" => Some(Self::SeqNth),
            "seq_rev" => Some(Self::SeqRev),
            "seq_unit" => Some(Self::SeqUnit),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PureFnParam {
    pub name: String,
    pub ty: SpecTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PureFnDef {
    pub name: String,
    pub params: Vec<PureFnParam>,
    pub result_ty: SpecTy,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GhostStmt {
    Assert(Expr),
    Assume(Expr),
    Call { name: String, args: Vec<Expr> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LemmaDef {
    pub name: String,
    pub params: Vec<PureFnParam>,
    pub req: Expr,
    pub ens: Expr,
    pub body: Vec<GhostStmt>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GhostBlock {
    pub pure_fns: Vec<PureFnDef>,
    pub lemmas: Vec<LemmaDef>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructTy {
    pub name: String,
    pub fields: Vec<StructFieldTy>,
}

impl StructTy {
    pub fn field(&self, name: &str) -> Option<(usize, &StructFieldTy)> {
        self.fields
            .iter()
            .enumerate()
            .find(|(_, field)| field.name == name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructFieldTy {
    pub name: String,
    pub ty: SpecTy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
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

pub fn parse_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    let decoded = decode_string_literal(kind, text)?;
    parse_templated_expr(kind, &decoded)
}

pub fn parse_templated_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    let expanded = expand_template(kind, text)?;
    parse_raw_expr(kind, &expanded)
}

pub fn parse_raw_expr(_kind: &str, text: &str) -> Result<Expr, ParseError> {
    let mut parser = Parser::new(text)?;
    let expr = parser.parse_expr()?;
    parser.expect_end()?;
    Ok(expr)
}

fn decode_string_literal(kind: &str, text: &str) -> Result<String, ParseError> {
    let Some(inner) = text
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
    else {
        return Err(ParseError::new(format!(
            "failed to parse //@ {kind} predicate: expected string literal"
        )));
    };

    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        let Some(esc) = chars.next() else {
            return Err(ParseError::new(format!(
                "failed to parse //@ {kind} predicate: trailing escape in string literal"
            )));
        };
        match esc {
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '0' => out.push('\0'),
            _ => {
                return Err(ParseError::new(format!(
                    "failed to parse //@ {kind} predicate: unsupported escape `\\{esc}`"
                )));
            }
        }
    }

    Ok(out)
}

fn expand_template(kind: &str, raw: &str) -> Result<String, ParseError> {
    let mut out = String::new();
    let mut chars = raw.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '{' => {
                if chars.peek() == Some(&'{') {
                    chars.next();
                    out.push('{');
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
                    return Err(ParseError::new(format!(
                        "unclosed `{{` in //@ {kind} template"
                    )));
                }
                let inner = inner.trim();
                if inner.is_empty() {
                    return Err(ParseError::new(format!(
                        "empty interpolation in //@ {kind} template"
                    )));
                }
                out.push('(');
                out.push_str(inner);
                out.push(')');
            }
            '}' => {
                if chars.peek() == Some(&'}') {
                    chars.next();
                    out.push('}');
                } else {
                    return Err(ParseError::new(format!(
                        "unmatched `}}` in //@ {kind} template"
                    )));
                }
            }
            _ => out.push(ch),
        }
    }
    Ok(out)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Int(IntLiteral),
    Bool(bool),
    LParen,
    RParen,
    Comma,
    Dot,
    Question,
    Plus,
    Minus,
    Star,
    Bang,
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
            ',' => {
                chars.next();
                tokens.push(Token::Comma);
            }
            '.' => {
                chars.next();
                tokens.push(Token::Dot);
            }
            '?' => {
                chars.next();
                tokens.push(Token::Question);
            }
            '+' => {
                chars.next();
                tokens.push(Token::Plus);
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
                if chars.next() == Some('=') {
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
                if chars.next() == Some('&') {
                    tokens.push(Token::AndAnd);
                } else {
                    return Err(ParseError::new("unexpected `&` in spec expression"));
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
}

impl Parser {
    fn new(text: &str) -> Result<Self, ParseError> {
        Ok(Self {
            tokens: lex_expr(text)?,
            cursor: 0,
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
        let mut expr = self.parse_add()?;
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
            let rhs = self.parse_add()?;
            expr = Expr::Binary {
                op,
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
        while self.eat(&Token::Dot) {
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
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match self.next().cloned() {
            Some(Token::Bool(value)) => Ok(Expr::Bool(value)),
            Some(Token::Int(value)) => Ok(Expr::Int(value)),
            Some(Token::Question) => {
                let Some(Token::Ident(ident)) = self.next().cloned() else {
                    return Err(ParseError::new("expected identifier after `?`"));
                };
                Ok(Expr::Bind(ident))
            }
            Some(Token::Ident(ident)) => {
                if !ident.starts_with("__") && self.eat(&Token::LParen) {
                    let mut args = Vec::new();
                    if !self.eat(&Token::RParen) {
                        loop {
                            args.push(self.parse_expr()?);
                            if self.eat(&Token::RParen) {
                                break;
                            }
                            self.expect(&Token::Comma)?;
                        }
                    }
                    Ok(Expr::Call { func: ident, args })
                } else {
                    Ok(Expr::Var(ident))
                }
            }
            Some(Token::LParen) => {
                let expr = self.parse_expr()?;
                self.expect(&Token::RParen)?;
                Ok(expr)
            }
            _ => Err(ParseError::new("expected a spec expression")),
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
    let mut parser = PureFnParser::new(text);
    let mut block = GhostBlock::default();
    while parser.skip_ws() {
        match parser.parse_item()? {
            GhostItem::PureFn(def) => block.pure_fns.push(def),
            GhostItem::Lemma(def) => block.lemmas.push(def),
        }
    }
    Ok(block)
}

enum GhostItem {
    PureFn(PureFnDef),
    Lemma(LemmaDef),
}

struct PureFnParser<'a> {
    text: &'a str,
    cursor: usize,
}

impl<'a> PureFnParser<'a> {
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
        self.expect_keyword("fn")?;
        let name = self.parse_ident()?;
        self.expect_char('(')?;
        let mut params = Vec::new();
        self.skip_ws();
        if !self.eat_char(')') {
            loop {
                let param_name = self.parse_ident()?;
                self.expect_char(':')?;
                let ty = self.parse_spec_ty()?;
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
            return Ok(GhostItem::PureFn(self.parse_pure_fn_def(name, params)?));
        }
        Ok(GhostItem::Lemma(self.parse_lemma_def(name, params)?))
    }

    fn parse_pure_fn_def(
        &mut self,
        name: String,
        params: Vec<PureFnParam>,
    ) -> Result<PureFnDef, ParseError> {
        self.expect_arrow()?;
        let result_ty = self.parse_spec_ty()?;
        self.expect_char('{')?;
        let body = self.parse_braced_body()?;
        Ok(PureFnDef {
            name,
            params,
            result_ty,
            body: parse_raw_expr("pure function body", body.trim())?,
        })
    }

    fn parse_lemma_def(
        &mut self,
        name: String,
        params: Vec<PureFnParam>,
    ) -> Result<LemmaDef, ParseError> {
        self.expect_keyword("req")?;
        let req = self.parse_quoted_expr("lemma req")?;
        self.expect_keyword("ens")?;
        let ens = self.parse_quoted_expr("lemma ens")?;
        self.expect_char('{')?;
        let body = self.parse_braced_body()?;
        Ok(LemmaDef {
            name,
            params,
            req,
            ens,
            body: self.parse_lemma_body(body)?,
        })
    }

    fn parse_spec_ty(&mut self) -> Result<SpecTy, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            "bool" => Ok(SpecTy::Bool),
            "i8" => Ok(SpecTy::I8),
            "i16" => Ok(SpecTy::I16),
            "i32" => Ok(SpecTy::I32),
            "i64" => Ok(SpecTy::I64),
            "isize" => Ok(SpecTy::Isize),
            "u8" => Ok(SpecTy::U8),
            "u16" => Ok(SpecTy::U16),
            "u32" => Ok(SpecTy::U32),
            "u64" => Ok(SpecTy::U64),
            "usize" => Ok(SpecTy::Usize),
            "Seq" => {
                self.expect_char('<')?;
                let inner = self.parse_spec_ty()?;
                self.expect_char('>')?;
                Ok(SpecTy::Seq(Box::new(inner)))
            }
            _ => Err(ParseError::new(format!(
                "unsupported pure function type `{ident}`"
            ))),
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

    fn parse_lemma_body(&self, body: &str) -> Result<Vec<GhostStmt>, ParseError> {
        let mut stmts = Vec::new();
        let mut cursor = 0usize;
        while cursor < body.len() {
            while let Some(ch) = body[cursor..].chars().next() {
                if ch.is_whitespace() {
                    cursor += ch.len_utf8();
                } else {
                    break;
                }
                if cursor >= body.len() {
                    return Ok(stmts);
                }
            }
            if cursor >= body.len() {
                break;
            }
            if body[cursor..].starts_with("assert") {
                cursor += "assert".len();
                let (expr_text, next) = self.parse_quoted_literal(body, cursor)?;
                cursor = self.expect_stmt_terminator(body, next)?;
                let expanded = expand_template("lemma assert", &expr_text)?;
                stmts.push(GhostStmt::Assert(parse_raw_expr(
                    "lemma assert",
                    &expanded,
                )?));
                continue;
            }
            if body[cursor..].starts_with("assume") {
                cursor += "assume".len();
                let (expr_text, next) = self.parse_quoted_literal(body, cursor)?;
                cursor = self.expect_stmt_terminator(body, next)?;
                let expanded = expand_template("lemma assume", &expr_text)?;
                stmts.push(GhostStmt::Assume(parse_raw_expr(
                    "lemma assume",
                    &expanded,
                )?));
                continue;
            }

            let name_start = cursor;
            let mut chars = body[cursor..].chars();
            let Some(first) = chars.next() else {
                break;
            };
            if !(first.is_ascii_alphabetic() || first == '_') {
                return Err(ParseError::new("expected lemma statement"));
            }
            cursor += first.len_utf8();
            while let Some(ch) = body[cursor..].chars().next() {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    cursor += ch.len_utf8();
                } else {
                    break;
                }
            }
            let name = body[name_start..cursor].to_owned();
            while let Some(ch) = body[cursor..].chars().next() {
                if ch.is_whitespace() {
                    cursor += ch.len_utf8();
                } else {
                    break;
                }
            }
            if body[cursor..].chars().next() != Some('(') {
                return Err(ParseError::new("expected `(` in lemma call"));
            }
            let (args_body, next) = self.parse_paren_body(body, cursor)?;
            cursor = self.expect_stmt_terminator(body, next)?;
            let args = self.parse_call_args(args_body)?;
            stmts.push(GhostStmt::Call { name, args });
        }
        Ok(stmts)
    }

    fn parse_call_args(&self, text: &str) -> Result<Vec<Expr>, ParseError> {
        let mut args = Vec::new();
        let mut cursor = 0usize;
        let mut current_start = 0usize;
        let mut depth = 0usize;
        while cursor < text.len() {
            let ch = text[cursor..].chars().next().expect("char");
            match ch {
                '(' | '{' | '[' | '<' => depth += 1,
                ')' | '}' | ']' | '>' => {
                    depth = depth.saturating_sub(1);
                }
                ',' if depth == 0 => {
                    let arg = text[current_start..cursor].trim();
                    if !arg.is_empty() {
                        args.push(parse_raw_expr("lemma call argument", arg)?);
                    }
                    cursor += ch.len_utf8();
                    current_start = cursor;
                    continue;
                }
                _ => {}
            }
            cursor += ch.len_utf8();
        }
        let tail = text[current_start..].trim();
        if !tail.is_empty() {
            args.push(parse_raw_expr("lemma call argument", tail)?);
        }
        Ok(args)
    }

    fn parse_quoted_expr(&mut self, kind: &str) -> Result<Expr, ParseError> {
        let (text, next) = self.parse_quoted_literal(self.text, self.cursor)?;
        self.cursor = next;
        let expanded = expand_template(kind, &text)?;
        parse_raw_expr(kind, &expanded)
    }

    fn parse_quoted_literal(
        &self,
        text: &'a str,
        mut cursor: usize,
    ) -> Result<(String, usize), ParseError> {
        while let Some(ch) = text[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        if text[cursor..].chars().next() != Some('"') {
            return Err(ParseError::new("expected string literal"));
        }
        cursor += 1;
        let start = cursor;
        while let Some(ch) = text[cursor..].chars().next() {
            if ch == '"' {
                return Ok((text[start..cursor].to_owned(), cursor + 1));
            }
            cursor += ch.len_utf8();
        }
        Err(ParseError::new("unterminated string literal"))
    }

    fn parse_paren_body(
        &self,
        text: &'a str,
        open_paren: usize,
    ) -> Result<(&'a str, usize), ParseError> {
        let mut cursor = open_paren;
        let mut depth = 0usize;
        let body_start = open_paren + 1;
        while cursor < text.len() {
            let ch = text[cursor..].chars().next().expect("char");
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok((&text[body_start..cursor], cursor + 1));
                    }
                }
                _ => {}
            }
            cursor += ch.len_utf8();
        }
        Err(ParseError::new("unclosed `(` in lemma call"))
    }

    fn expect_stmt_terminator(&self, text: &str, mut cursor: usize) -> Result<usize, ParseError> {
        while let Some(ch) = text[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }
        if text[cursor..].chars().next() != Some(';') {
            return Err(ParseError::new("expected `;` after lemma statement"));
        }
        Ok(cursor + 1)
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
        if self.text[self.cursor..].starts_with(keyword) {
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
}

#[cfg(test)]
mod tests {
    use super::{
        BinaryOp, Expr, GhostBlock, GhostStmt, IntLiteral, IntSuffix, LemmaDef, PureFnDef,
        PureFnParam, SpecTy, UnaryOp, parse_expr, parse_ghost_block, parse_pure_fn_block,
    };

    #[test]
    fn parses_deref_and_fin() {
        let expr = parse_expr("assert", r#""*{x} == {y}.fin""#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Deref {
                    base: Box::new(Expr::Var("x".to_owned())),
                }),
                rhs: Box::new(Expr::Field {
                    base: Box::new(Expr::Var("y".to_owned())),
                    name: "fin".to_owned(),
                }),
            }
        );
    }

    #[test]
    fn parses_tuple_projection() {
        let expr = parse_expr("assert", r#""{x}.0 == 1i32""#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::TupleField {
                    base: Box::new(Expr::Var("x".to_owned())),
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
    fn parses_bind_expression() {
        let expr = parse_expr("assert", r#""?x == 3""#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Bind("x".to_owned())),
                rhs: Box::new(Expr::Int(IntLiteral {
                    digits: "3".to_owned(),
                    suffix: None,
                })),
            }
        );
    }

    #[test]
    fn keeps_operator_precedence() {
        let expr = parse_expr("assert", r#""!false || 1 + 2 * 3 == 7""#).expect("expr");
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
        let expr = parse_expr("assert", r#""{x}.left == 1i32""#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Field {
                    base: Box::new(Expr::Var("x".to_owned())),
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
        let expr = parse_expr("assert", r#""18446744073709551615u64 == 0usize""#).expect("expr");
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
        let expr = parse_expr("assert", r#""seq_rev({xs}) == {ys}""#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Call {
                    func: "seq_rev".to_owned(),
                    args: vec![Expr::Var("xs".to_owned())],
                }),
                rhs: Box::new(Expr::Var("ys".to_owned())),
            }
        );
    }

    #[test]
    fn parses_pure_function_block() {
        let defs = parse_pure_fn_block(
            r#"
fn is_rev(x: Seq<i32>, y: Seq<i32>) -> bool {
    seq_rev(x) == y
}
"#,
        )
        .expect("pure fn block");
        assert_eq!(
            defs,
            vec![PureFnDef {
                name: "is_rev".to_owned(),
                params: vec![
                    PureFnParam {
                        name: "x".to_owned(),
                        ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                    },
                    PureFnParam {
                        name: "y".to_owned(),
                        ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                    },
                ],
                result_ty: SpecTy::Bool,
                body: Expr::Binary {
                    op: BinaryOp::Eq,
                    lhs: Box::new(Expr::Call {
                        func: "seq_rev".to_owned(),
                        args: vec![Expr::Var("x".to_owned())],
                    }),
                    rhs: Box::new(Expr::Var("y".to_owned())),
                },
            }]
        );
    }

    #[test]
    fn parses_lemma_block() {
        let block = parse_ghost_block(
            r#"
fn is_rev(x: Seq<i32>, y: Seq<i32>) -> bool {
    seq_rev(x) == y
}

fn rev_done(orig: Seq<i32>, cur: Seq<i32>)
  req "true"
  ens "is_rev(orig, cur)"
{
    assert "is_rev(orig, cur)";
}
"#,
        )
        .expect("ghost block");
        assert_eq!(
            block,
            GhostBlock {
                pure_fns: vec![PureFnDef {
                    name: "is_rev".to_owned(),
                    params: vec![
                        PureFnParam {
                            name: "x".to_owned(),
                            ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                        },
                        PureFnParam {
                            name: "y".to_owned(),
                            ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                        },
                    ],
                    result_ty: SpecTy::Bool,
                    body: Expr::Binary {
                        op: BinaryOp::Eq,
                        lhs: Box::new(Expr::Call {
                            func: "seq_rev".to_owned(),
                            args: vec![Expr::Var("x".to_owned())],
                        }),
                        rhs: Box::new(Expr::Var("y".to_owned())),
                    },
                }],
                lemmas: vec![LemmaDef {
                    name: "rev_done".to_owned(),
                    params: vec![
                        PureFnParam {
                            name: "orig".to_owned(),
                            ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                        },
                        PureFnParam {
                            name: "cur".to_owned(),
                            ty: SpecTy::Seq(Box::new(SpecTy::I32)),
                        },
                    ],
                    req: Expr::Bool(true),
                    ens: Expr::Call {
                        func: "is_rev".to_owned(),
                        args: vec![Expr::Var("orig".to_owned()), Expr::Var("cur".to_owned())],
                    },
                    body: vec![GhostStmt::Assert(Expr::Call {
                        func: "is_rev".to_owned(),
                        args: vec![Expr::Var("orig".to_owned()), Expr::Var("cur".to_owned())],
                    })],
                }],
            }
        );
    }
}
