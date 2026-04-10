#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecExpr {
    Bool(bool),
    Int(i64),
    Var(String),
    Result,
    Prophecy(String),
    Field {
        base: Box<SpecExpr>,
        index: usize,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecParseError {
    message: String,
}

impl SpecParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for SpecParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for SpecParseError {}

pub fn parse_spec_expr(kind: &str, text: &str) -> Result<SpecExpr, SpecParseError> {
    let decoded = decode_string_literal(kind, text)?;
    let expanded = expand_spec_template(kind, &decoded)?;
    let mut parser = Parser::new(&expanded)?;
    let expr = parser.parse_expr()?;
    parser.expect_end()?;
    Ok(expr)
}

fn decode_string_literal(kind: &str, text: &str) -> Result<String, SpecParseError> {
    let Some(inner) = text
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
    else {
        return Err(SpecParseError::new(format!(
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
            return Err(SpecParseError::new(format!(
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
                return Err(SpecParseError::new(format!(
                    "failed to parse //@ {kind} predicate: unsupported escape `\\{esc}`"
                )));
            }
        }
    }

    Ok(out)
}

fn expand_spec_template(kind: &str, raw: &str) -> Result<String, SpecParseError> {
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
                    return Err(SpecParseError::new(format!(
                        "unclosed `{{` in //@ {kind} template"
                    )));
                }
                let inner = inner.trim();
                if inner.is_empty() {
                    return Err(SpecParseError::new(format!(
                        "empty interpolation in //@ {kind} template"
                    )));
                }
                if inner.strip_prefix("^:").is_some() {
                    return Err(SpecParseError::new(format!(
                        "prophecy interpolation is unsupported in //@ {} templates; use `.cur` / `.fin`",
                        kind
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
                    return Err(SpecParseError::new(format!(
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
    Int(i64),
    Bool(bool),
    LParen,
    RParen,
    Comma,
    Dot,
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

fn lex_expr(text: &str) -> Result<Vec<Token>, SpecParseError> {
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
                let value = digits
                    .parse::<i64>()
                    .map_err(|_| SpecParseError::new("integer literal is too large"))?;
                tokens.push(Token::Int(value));
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
                    return Err(SpecParseError::new("unexpected `=` in spec expression"));
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
                    return Err(SpecParseError::new("unexpected `&` in spec expression"));
                }
            }
            '|' => {
                chars.next();
                if chars.next() == Some('|') {
                    tokens.push(Token::OrOr);
                } else {
                    return Err(SpecParseError::new("unexpected `|` in spec expression"));
                }
            }
            _ => {
                return Err(SpecParseError::new(format!(
                    "unexpected character `{ch}` in spec expression"
                )));
            }
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    cursor: usize,
}

impl Parser {
    fn new(text: &str) -> Result<Self, SpecParseError> {
        Ok(Self {
            tokens: lex_expr(text)?,
            cursor: 0,
        })
    }

    fn parse_expr(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.parse_or()
    }

    fn expect_end(&self) -> Result<(), SpecParseError> {
        if self.cursor == self.tokens.len() {
            Ok(())
        } else {
            Err(SpecParseError::new(
                "unexpected trailing tokens in spec expression",
            ))
        }
    }

    fn parse_or(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_and()?;
        while self.eat(&Token::OrOr) {
            let rhs = self.parse_and()?;
            expr = SpecExpr::Binary {
                op: SpecBinaryOp::Or,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_and(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_eq()?;
        while self.eat(&Token::AndAnd) {
            let rhs = self.parse_eq()?;
            expr = SpecExpr::Binary {
                op: SpecBinaryOp::And,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_eq(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_cmp()?;
        loop {
            let op = if self.eat(&Token::EqEq) {
                Some(SpecBinaryOp::Eq)
            } else if self.eat(&Token::Ne) {
                Some(SpecBinaryOp::Ne)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_cmp()?;
            expr = SpecExpr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_cmp(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_add()?;
        loop {
            let op = if self.eat(&Token::Lt) {
                Some(SpecBinaryOp::Lt)
            } else if self.eat(&Token::Le) {
                Some(SpecBinaryOp::Le)
            } else if self.eat(&Token::Gt) {
                Some(SpecBinaryOp::Gt)
            } else if self.eat(&Token::Ge) {
                Some(SpecBinaryOp::Ge)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_add()?;
            expr = SpecExpr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_add(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_mul()?;
        loop {
            let op = if self.eat(&Token::Plus) {
                Some(SpecBinaryOp::Add)
            } else if self.eat(&Token::Minus) {
                Some(SpecBinaryOp::Sub)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_mul()?;
            expr = SpecExpr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_mul(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_unary()?;
        while self.eat(&Token::Star) {
            let rhs = self.parse_unary()?;
            expr = SpecExpr::Binary {
                op: SpecBinaryOp::Mul,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<SpecExpr, SpecParseError> {
        if self.eat(&Token::Bang) {
            return Ok(SpecExpr::Unary {
                op: SpecUnaryOp::Not,
                arg: Box::new(self.parse_unary()?),
            });
        }
        if self.eat(&Token::Minus) {
            return Ok(SpecExpr::Unary {
                op: SpecUnaryOp::Neg,
                arg: Box::new(self.parse_unary()?),
            });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<SpecExpr, SpecParseError> {
        let mut expr = self.parse_primary()?;
        while self.eat(&Token::Dot) {
            expr = SpecExpr::Field {
                base: Box::new(expr),
                index: self.parse_field_index()?,
            };
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<SpecExpr, SpecParseError> {
        match self.next() {
            Some(Token::Bool(value)) => Ok(SpecExpr::Bool(*value)),
            Some(Token::Int(value)) => Ok(SpecExpr::Int(*value)),
            Some(Token::Ident(ident)) if ident == "__prophecy" => self.parse_prophecy_call(),
            Some(Token::Ident(ident)) if ident == "result" => Ok(SpecExpr::Result),
            Some(Token::Ident(ident)) => Ok(SpecExpr::Var(ident.clone())),
            Some(Token::LParen) => {
                let expr = self.parse_expr()?;
                self.expect(&Token::RParen)?;
                Ok(expr)
            }
            _ => Err(SpecParseError::new("expected a spec expression")),
        }
    }

    fn parse_prophecy_call(&mut self) -> Result<SpecExpr, SpecParseError> {
        self.expect(&Token::LParen)?;
        let Some(Token::Ident(ident)) = self.next() else {
            return Err(SpecParseError::new(
                "unsupported prophecy argument in spec expression",
            ));
        };
        let ident = ident.clone();
        self.expect(&Token::RParen)?;
        Ok(SpecExpr::Prophecy(ident))
    }

    fn parse_field_index(&mut self) -> Result<usize, SpecParseError> {
        match self.next() {
            Some(Token::Int(value)) if *value >= 0 => Ok(*value as usize),
            Some(Token::Ident(ident)) if ident == "cur" => Ok(0),
            Some(Token::Ident(ident)) if ident == "fin" => Ok(1),
            _ => Err(SpecParseError::new(
                "unsupported field access in spec expression",
            )),
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

    fn expect(&mut self, token: &Token) -> Result<(), SpecParseError> {
        if self.eat(token) {
            Ok(())
        } else {
            Err(SpecParseError::new(format!("expected token {:?}", token)))
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
    use super::{SpecBinaryOp, SpecExpr, SpecUnaryOp, parse_spec_expr};

    #[test]
    fn parses_template_interpolation_without_syn() {
        let expr = parse_spec_expr("assert", r#""{x}.0.cur == 1""#).expect("expr");
        assert_eq!(
            expr,
            SpecExpr::Binary {
                op: SpecBinaryOp::Eq,
                lhs: Box::new(SpecExpr::Field {
                    base: Box::new(SpecExpr::Field {
                        base: Box::new(SpecExpr::Var("x".to_owned())),
                        index: 0,
                    }),
                    index: 0,
                }),
                rhs: Box::new(SpecExpr::Int(1)),
            }
        );
    }

    #[test]
    fn parses_result_only_in_surface_ast() {
        let expr = parse_spec_expr("ens", r#""{result} == 3""#).expect("expr");
        assert_eq!(
            expr,
            SpecExpr::Binary {
                op: SpecBinaryOp::Eq,
                lhs: Box::new(SpecExpr::Result),
                rhs: Box::new(SpecExpr::Int(3)),
            }
        );
    }

    #[test]
    fn parses_prophecy_call() {
        let expr = parse_spec_expr("inv", r#""__prophecy(x).fin >= 0""#).expect("expr");
        assert_eq!(
            expr,
            SpecExpr::Binary {
                op: SpecBinaryOp::Ge,
                lhs: Box::new(SpecExpr::Field {
                    base: Box::new(SpecExpr::Prophecy("x".to_owned())),
                    index: 1,
                }),
                rhs: Box::new(SpecExpr::Int(0)),
            }
        );
    }

    #[test]
    fn keeps_operator_precedence() {
        let expr = parse_spec_expr("assert", r#""!false || 1 + 2 * 3 == 7""#).expect("expr");
        assert_eq!(
            expr,
            SpecExpr::Binary {
                op: SpecBinaryOp::Or,
                lhs: Box::new(SpecExpr::Unary {
                    op: SpecUnaryOp::Not,
                    arg: Box::new(SpecExpr::Bool(false)),
                }),
                rhs: Box::new(SpecExpr::Binary {
                    op: SpecBinaryOp::Eq,
                    lhs: Box::new(SpecExpr::Binary {
                        op: SpecBinaryOp::Add,
                        lhs: Box::new(SpecExpr::Int(1)),
                        rhs: Box::new(SpecExpr::Binary {
                            op: SpecBinaryOp::Mul,
                            lhs: Box::new(SpecExpr::Int(2)),
                            rhs: Box::new(SpecExpr::Int(3)),
                        }),
                    }),
                    rhs: Box::new(SpecExpr::Int(7)),
                }),
            }
        );
    }

    #[test]
    fn rejects_prophecy_interpolation() {
        let err = parse_spec_expr("req", r#""{^:x}""#).expect_err("should fail");
        assert!(err.to_string().contains("prophecy interpolation"));
    }
}
