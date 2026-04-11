#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Bool(bool),
    Int(IntLiteral),
    Var(String),
    Bind(String),
    TupleField {
        base: Box<Expr>,
        index: usize,
    },
    Deref {
        base: Box<Expr>,
    },
    Fin {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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
    Ref(Box<SpecTy>),
    Mut(Box<SpecTy>),
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
    let expanded = expand_template(kind, &decoded)?;
    let mut parser = Parser::new(&expanded)?;
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
                Some(Token::Ident(ident)) if ident == "fin" => Expr::Fin {
                    base: Box::new(expr),
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
        match self.next() {
            Some(Token::Bool(value)) => Ok(Expr::Bool(*value)),
            Some(Token::Int(value)) => Ok(Expr::Int(value.clone())),
            Some(Token::Question) => {
                let Some(Token::Ident(ident)) = self.next() else {
                    return Err(ParseError::new("expected identifier after `?`"));
                };
                Ok(Expr::Bind(ident.clone()))
            }
            Some(Token::Ident(ident)) => Ok(Expr::Var(ident.clone())),
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
mod tests {
    use super::{BinaryOp, Expr, IntLiteral, IntSuffix, UnaryOp, parse_expr};

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
                rhs: Box::new(Expr::Fin {
                    base: Box::new(Expr::Var("y".to_owned())),
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
    fn rejects_cur_accessor() {
        let err = parse_expr("assert", r#""{x}.cur""#).expect_err("should fail");
        assert!(
            err.to_string()
                .contains("unsupported field access in spec expression")
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
}
