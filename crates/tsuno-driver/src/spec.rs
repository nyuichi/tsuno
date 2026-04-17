#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Bool(bool),
    Int(IntLiteral),
    Var(String),
    Bind(String),
    Call {
        func: String,
        type_args: Vec<SpecTy>,
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
    CtorCall {
        enum_name: String,
        ctor_name: String,
        ctor_index: usize,
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
    Tuple(Vec<SpecTy>),
    Struct(StructTy),
    Named { name: String, args: Vec<SpecTy> },
    TypeParam(String),
    Ref(Box<SpecTy>),
    Mut(Box<SpecTy>),
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
    pub enums: Vec<EnumDef>,
    pub pure_fns: Vec<PureFnDef>,
    pub lemmas: Vec<LemmaDef>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumDef {
    pub name: String,
    pub type_params: Vec<String>,
    pub ctors: Vec<EnumCtorDef>,
}

impl EnumDef {
    pub fn ctor(&self, name: &str) -> Option<(usize, &EnumCtorDef)> {
        self.ctors
            .iter()
            .enumerate()
            .find(|(_, ctor)| ctor.name == name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumCtorDef {
    pub name: String,
    pub fields: Vec<SpecTy>,
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

#[cfg(test)]
pub fn parse_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    parse_source_expr(kind, text)
}

pub fn parse_source_expr(kind: &str, text: &str) -> Result<Expr, ParseError> {
    if let Some(decoded) = decode_legacy_string_literal(text)? {
        return parse_templated_expr(kind, &decoded);
    }
    parse_templated_expr(kind, text.trim())
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

fn decode_legacy_string_literal(text: &str) -> Result<Option<String>, ParseError> {
    let Some(inner) = text
        .trim()
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
    else {
        return Ok(None);
    };

    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        let Some(esc) = chars.next() else {
            return Err(ParseError::new(
                "failed to parse spec expression: trailing escape in string literal".to_string(),
            ));
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
                    "failed to parse spec expression: unsupported escape `\\{esc}`"
                )));
            }
        }
    }

    Ok(Some(out))
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
    ColonColon,
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
            ':' => {
                chars.next();
                if chars.next() == Some(':') {
                    tokens.push(Token::ColonColon);
                } else {
                    return Err(ParseError::new("unexpected `:` in spec expression"));
                }
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

    fn parse_token_spec_ty(&mut self) -> Result<SpecTy, ParseError> {
        let Some(Token::Ident(ident)) = self.next().cloned() else {
            return Err(ParseError::new("expected a type argument"));
        };
        let args = if self.eat(&Token::Lt) {
            let mut args = Vec::new();
            if !self.eat(&Token::Gt) {
                loop {
                    args.push(self.parse_token_spec_ty()?);
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
            "bool" if args.is_empty() => Ok(SpecTy::Bool),
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
            _ => Ok(SpecTy::Named { name: ident, args }),
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
                args.push(self.parse_token_spec_ty()?);
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
            Some(Token::Question) => {
                let Some(Token::Ident(ident)) = self.next().cloned() else {
                    return Err(ParseError::new("expected identifier after `?`"));
                };
                Ok(Expr::Bind(ident))
            }
            Some(Token::Ident(ident)) => {
                let type_args = self.try_parse_call_type_args()?.unwrap_or_default();
                if self.eat(&Token::ColonColon) {
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
            GhostItem::Enum(def) => block.enums.push(def),
            GhostItem::PureFn(def) => block.pure_fns.push(def),
            GhostItem::Lemma(def) => block.lemmas.push(def),
        }
    }
    Ok(block)
}

enum GhostItem {
    Enum(EnumDef),
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
        if self.starts_with_keyword("enum") {
            self.expect_keyword("enum")?;
            return Ok(GhostItem::Enum(self.parse_enum_def()?));
        }
        self.expect_keyword("fn")?;
        let name = self.parse_ident()?;
        self.expect_char('(')?;
        let mut params = Vec::new();
        self.skip_ws();
        if !self.eat_char(')') {
            loop {
                let param_name = self.parse_ident()?;
                self.expect_char(':')?;
                let ty = self.parse_spec_ty_with_params(&[])?;
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
                        fields.push(self.parse_spec_ty_with_params(&type_params)?);
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

    fn parse_pure_fn_def(
        &mut self,
        name: String,
        params: Vec<PureFnParam>,
    ) -> Result<PureFnDef, ParseError> {
        self.expect_arrow()?;
        let result_ty = self.parse_spec_ty_with_params(&[])?;
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
        let req = self.parse_line_expr("lemma req")?;
        self.expect_keyword("ens")?;
        let ens = self.parse_line_expr("lemma ens")?;
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

    fn parse_spec_ty_with_params(&mut self, type_params: &[String]) -> Result<SpecTy, ParseError> {
        let ident = self.parse_ident()?;
        self.skip_ws();
        let args = if self.eat_char('<') {
            let mut args = Vec::new();
            self.skip_ws();
            if !self.eat_char('>') {
                loop {
                    args.push(self.parse_spec_ty_with_params(type_params)?);
                    self.skip_ws();
                    if self.eat_char('>') {
                        break;
                    }
                    self.expect_char(',')?;
                }
            }
            args
        } else {
            Vec::new()
        };
        match ident.as_str() {
            "bool" if args.is_empty() => Ok(SpecTy::Bool),
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
            _ if args.is_empty() && type_params.iter().any(|param| param == &ident) => {
                Ok(SpecTy::TypeParam(ident))
            }
            _ => Ok(SpecTy::Named { name: ident, args }),
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
                let (expr_text, next) = self.parse_stmt_expr_text(body, cursor)?;
                cursor = next;
                stmts.push(GhostStmt::Assert(parse_source_expr(
                    "lemma assert",
                    expr_text,
                )?));
                continue;
            }
            if body[cursor..].starts_with("assume") {
                cursor += "assume".len();
                let (expr_text, next) = self.parse_stmt_expr_text(body, cursor)?;
                cursor = next;
                stmts.push(GhostStmt::Assume(parse_source_expr(
                    "lemma assume",
                    expr_text,
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
            if !body[cursor..].starts_with('(') {
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
                        args.push(parse_source_expr("lemma call argument", arg)?);
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
            args.push(parse_source_expr("lemma call argument", tail)?);
        }
        Ok(args)
    }

    fn parse_line_expr(&mut self, kind: &str) -> Result<Expr, ParseError> {
        let (text, next) = self.parse_line_expr_text(self.text, self.cursor)?;
        self.cursor = next;
        parse_source_expr(kind, text)
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
        if !text[cursor..].starts_with(';') {
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
        BinaryOp, EnumCtorDef, EnumDef, Expr, GhostBlock, GhostStmt, IntLiteral, IntSuffix,
        LemmaDef, PureFnDef, PureFnParam, SpecTy, UnaryOp, parse_expr, parse_ghost_block,
        parse_pure_fn_block,
    };

    #[test]
    fn parses_deref_and_fin() {
        let expr = parse_expr("assert", r#"*{x} == {y}.fin"#).expect("expr");
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
        let expr = parse_expr("assert", r#"{x}.0 == 1i32"#).expect("expr");
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
        let expr = parse_expr("assert", r#"?x == 3"#).expect("expr");
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
                    args: vec![Expr::Var("xs".to_owned())],
                }),
                rhs: Box::new(Expr::Var("ys".to_owned())),
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
    fn parses_statement_expression_with_trailing_semicolon() {
        let expr = super::parse_statement_expr("assert", r#"{x} == 1i32;"#).expect("expr");
        assert_eq!(
            expr,
            Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(Expr::Var("x".to_owned())),
                rhs: Box::new(Expr::Int(IntLiteral {
                    digits: "1".to_owned(),
                    suffix: Some(IntSuffix::I32),
                })),
            }
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
    fn parses_generic_named_types_in_pure_function_block() {
        let defs = parse_pure_fn_block(
            r#"
fn is_rev(x: Seq<i32>) -> bool {
    true
}
"#,
        )
        .expect("generic named type should parse");
        assert_eq!(
            defs[0].params[0].ty,
            SpecTy::Named {
                name: "Seq".to_owned(),
                args: vec![SpecTy::I32],
            }
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
                pure_fns: vec![PureFnDef {
                    name: "add1".to_owned(),
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
                    params: vec![PureFnParam {
                        name: "x".to_owned(),
                        ty: SpecTy::I32,
                    }],
                    req: Expr::Bool(true),
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
                                SpecTy::Named {
                                    name: "IntList".to_owned(),
                                    args: vec![],
                                },
                            ],
                        },
                    ],
                }],
                pure_fns: vec![PureFnDef {
                    name: "singleton".to_owned(),
                    params: vec![PureFnParam {
                        name: "x".to_owned(),
                        ty: SpecTy::I32,
                    }],
                    result_ty: SpecTy::Named {
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
}
