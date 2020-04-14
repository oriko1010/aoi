use crate::{
    ast::*,
    lexer::Lexer,
    token::{Token, TokenType},
};
use anyhow::{anyhow, bail, ensure, Result};
use std::iter::Peekable;

pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
}

const FUN_KEYWORD: &str = "fun";
const LET_KEYWORD: &str = "let";
const IF_KEYWORD: &str = "if";
const ELSE_KEYWORD: &str = "else";
const EXTERN_KEYWORD: &str = "extern";
const TRUE_KEYWORD: &str = "true";
const FALSE_KEYWORD: &str = "false";

impl<'a> Parser<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            lexer: Lexer::new(code).peekable(),
        }
    }

    pub fn parse_program(&mut self) -> Result<Program> {
        let mut expressions = Vec::with_capacity(32);
        loop {
            match self.parse_expression(0) {
                Ok(expression) => expressions.push(expression),
                Err(e) => {
                    eprintln!("{}", e);
                    break;
                }
            }
        }
        Ok(Program { expressions })
    }

    fn parse_expression(&mut self, precedence: u8) -> Result<Expression> {
        use TokenType::*;

        let mut lhs = match self.peek_token() {
            Token {
                ttype: Symbol,
                lexeme: FUN_KEYWORD,
                ..
            } => self.parse_function().map(Into::into),
            Token {
                ttype: Symbol,
                lexeme: LET_KEYWORD,
                ..
            } => self.parse_assign().map(Into::into),
            Token {
                ttype: Symbol,
                lexeme: IF_KEYWORD,
                ..
            } => self.parse_if().map(Into::into),
            Token {
                ttype: Symbol,
                lexeme: TRUE_KEYWORD | FALSE_KEYWORD,
                ..
            } => self.parse_bool().map(Into::into),
            Token { ttype: Symbol, .. } => self.parse_identifier().map(Into::into),
            Token { ttype: Number, .. } => self.parse_integer().map(Into::into),
            Token { ttype: String, .. } => self.parse_string().map(Into::into),
            Token {
                ttype: LeftParen, ..
            } => self.parse_grouping(),
            Token {
                ttype: LeftBrace, ..
            } => self.parse_block().map(Into::into),
            Token {
                ttype: Operator,
                lexeme,
                ..
            } => {
                let op = lexeme.to_string();
                self.expect_operator(&op)?;
                if let Some(prec) = unary_prefix_precedence(&op) {
                    let expression = self.parse_expression(prec)?;
                    Ok(UnaryOp::new(&op, expression).into())
                } else {
                    bail!("Unknown unary operator {}", op)
                }
            }
            Token { ttype: Eof, .. } => {
                bail!("Tried parsing expression but there were no tokens left")
            }
            token => bail!("Unknown expression token: {:?}", token),
        }?;

        loop {
            let peek = match self.peek_token() {
                Token { ttype: Eof, .. } => break,
                token => token,
            };

            if let Some((left, right)) = binary_precedence(peek) {
                if left < precedence {
                    break;
                }

                lhs = match peek {
                    Token {
                        ttype: LeftParen, ..
                    } => match lhs {
                        Expression::Identifier(identifier) => {
                            self.parse_call(identifier, None)?.into()
                        }
                        _ => bail!("This should probably never occur."),
                    },
                    Token {
                        ttype: Operator,
                        lexeme: ".",
                        ..
                    } => {
                        self.next_token();
                        let identifier = self.parse_identifier()?;
                        self.parse_call(identifier, Some(lhs))?.into()
                    }
                    Token {
                        ttype: Operator, ..
                    } => {
                        let op = self.next_token().lexeme.to_string();
                        let rhs = self.parse_expression(right)?;
                        BinaryOp::new(lhs, &op, rhs).into()
                    }
                    _ => return Ok(lhs),
                };
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    fn parse_grouping(&mut self) -> Result<Expression> {
        self.expect(TokenType::LeftParen, "(")?;
        let expression = self.parse_expression(0)?;
        self.expect(TokenType::RightParen, ")")?;
        Ok(expression)
    }

    fn parse_block(&mut self) -> Result<Block> {
        self.expect(TokenType::LeftBrace, "{")?;
        let mut expressions = Vec::with_capacity(4);
        loop {
            if self.peek_matches(TokenType::RightBrace, "}") {
                self.expect(TokenType::RightBrace, "}")?;
                break Ok(Block::new(expressions));
            } else {
                let expression = self.parse_expression(0)?;
                expressions.push(expression);
            }
        }
    }

    fn parse_integer(&mut self) -> Result<Integer> {
        let lexeme = self.next_token().lexeme;
        let value = lexeme
            .parse::<u64>()
            .map_err(|_| anyhow!("Error parsing integer literal"))?;
        Ok(Integer::from(value))
    }

    fn parse_string(&mut self) -> Result<String> {
        let lexeme = self.next_token().lexeme;
        ensure!(
            lexeme.starts_with('"') && lexeme.ends_with('"'),
            "Error parsing string literal"
        );
        Ok(String::new(&lexeme[1..lexeme.len() - 1]))
    }

    fn parse_identifier(&mut self) -> Result<Identifier> {
        let lexeme = self.next_token().lexeme;
        Ok(Identifier::from(lexeme))
    }

    fn parse_bool(&mut self) -> Result<Bool> {
        let lexeme = self.next_token().lexeme;
        match lexeme {
            TRUE_KEYWORD => Ok(Bool::new(true)),
            FALSE_KEYWORD => Ok(Bool::new(false)),
            _ => bail!("Error parsing boolean"),
        }
    }

    fn parse_operator(&mut self) -> Result<&str> {
        match self.next_token() {
            Token {
                ttype: TokenType::Operator,
                lexeme,
                ..
            } => Ok(lexeme),
            _ => bail!("Error parsing operator"),
        }
    }

    fn parse_function(&mut self) -> Result<Function> {
        self.expect_symbol(FUN_KEYWORD)?;

        let identifier = self.parse_identifier()?;
        let arguments = self.parse_argument_list()?;

        let return_type = if !self.peek_matches(TokenType::Operator, "->")
            && !self.peek_matches(TokenType::Symbol, EXTERN_KEYWORD)
        {
            self.parse_type()?
        } else {
            Type::new(Identifier::from("unit"), None)
        };

        if self.peek_matches(TokenType::Operator, "->") {
            self.expect_operator("->")?;
            let body = self.parse_expression(0)?;
            Ok(Function::new(
                FunctionSignature::new(identifier, arguments, return_type),
                body,
            ))
        } else {
            self.expect_symbol(EXTERN_KEYWORD)?;
            Ok(Function::new_extern(FunctionSignature::new(
                identifier,
                arguments,
                return_type,
            )))
        }
    }

    fn parse_if(&mut self) -> Result<If> {
        self.expect_symbol(IF_KEYWORD)?;
        let condition = self.parse_expression(0)?;
        let then = self.parse_expression(0)?;
        let other = if self.peek_matches(TokenType::Symbol, ELSE_KEYWORD) {
            self.expect(TokenType::Symbol, ELSE_KEYWORD)?;
            Some(self.parse_expression(0)?)
        } else {
            None
        };
        Ok(If::new(condition, then, other))
    }

    fn parse_assign(&mut self) -> Result<Assign> {
        self.expect_symbol(LET_KEYWORD)?;
        let identifier = self.parse_identifier()?;
        self.expect_operator("=")?;
        let expression = self.parse_expression(0)?;
        Ok(Assign::new(identifier, expression))
    }

    fn parse_argument_list(&mut self) -> Result<Vec<(Identifier, Type)>> {
        let mut arguments = Vec::new();
        self.expect(TokenType::LeftParen, "(")?;
        loop {
            if self.peek_matches(TokenType::RightParen, ")") {
                self.expect(TokenType::RightParen, ")")?;
                break Ok(arguments);
            } else {
                let identifier = self.parse_identifier()?;
                let argument_type = self.parse_type()?;
                arguments.push((identifier, argument_type));
                if self.peek_matches(TokenType::Operator, ",") {
                    self.expect(TokenType::Operator, ",")?;
                }
            }
        }
    }

    fn parse_call(&mut self, identifier: Identifier, first: Option<Expression>) -> Result<Call> {
        let mut arguments = Vec::new();
        if let Some(first) = first {
            arguments.push(first);
        }

        self.expect(TokenType::LeftParen, "(")?;
        loop {
            if self.peek_matches(TokenType::RightParen, ")") {
                self.expect(TokenType::RightParen, ")")?;
                break Ok(Call::new(identifier, arguments));
            } else {
                let argument = self.parse_expression(0)?;
                arguments.push(argument);
                if self.peek_matches(TokenType::Operator, ",") {
                    self.expect(TokenType::Operator, ",")?;
                }
            }
        }
    }

    fn parse_type(&mut self) -> Result<Type> {
        if self.peek_matches(TokenType::Operator, "*") {
            self.expect(TokenType::Operator, "*")?;
            let inner = self.parse_type()?;
            return Ok(Type::new(Identifier::from("Pointer"), Some(vec![inner])));
        } else if self.peek_matches(TokenType::Operator, "[]") {
            self.expect(TokenType::Operator, "[]")?;
            let inner = self.parse_type()?;
            return Ok(Type::new(Identifier::from("Slice"), Some(vec![inner])));
        } else {
            let identifier = self.parse_identifier()?;
            Ok(Type::new(identifier, None))
        }
    }

    fn next_token(&mut self) -> Token {
        self.lexer.next().unwrap_or(Token::EOF)
    }

    fn peek_token(&mut self) -> &Token {
        self.lexer.peek().unwrap_or(&Token::EOF)
    }

    fn peek_matches(&mut self, ttype: TokenType, lexeme: &str) -> bool {
        if let Some(peek) = self.lexer.peek() {
            if peek.ttype != ttype {
                return false;
            }
            if peek.lexeme != lexeme {
                return false;
            }
            true
        } else {
            false
        }
    }

    fn expect(&mut self, ttype: TokenType, lexeme: &str) -> Result<Token> {
        let next = self.next_token();
        ensure!(
            next.ttype == ttype,
            "Expected token type {:?}, found {:?}",
            ttype,
            next.ttype
        );
        ensure!(
            next.lexeme == lexeme,
            "Expected token lexeme {:?}, found {:?}",
            lexeme,
            next.lexeme
        );
        Ok(next)
    }

    #[inline]
    fn expect_symbol(&mut self, lexeme: &str) -> Result<Token> {
        self.expect(TokenType::Symbol, lexeme)
    }

    #[inline]
    fn expect_operator(&mut self, lexeme: &str) -> Result<Token> {
        self.expect(TokenType::Operator, lexeme)
    }
}

fn unary_prefix_precedence(op: &str) -> Option<u8> {
    match op {
        "!" | "+" | "-" | "++" | "--" => 12,
        _ => None?,
    }
    .into()
}

fn binary_precedence(token: &Token) -> Option<(u8, u8)> {
    use TokenType::*;
    match token {
        Token {
            ttype: Symbol,
            lexeme: LET_KEYWORD,
            ..
        } => (2, 1),
        Token {
            ttype: Operator,
            lexeme: "=",
            ..
        } => (2, 1),
        Token {
            ttype: Symbol,
            lexeme: FUN_KEYWORD,
            ..
        } => (4, 3),
        Token {
            ttype: Number | String,
            ..
        } => (6, 5),
        Token {
            ttype: Operator,
            lexeme: "+" | "-",
            ..
        } => (7, 8),
        Token {
            ttype: Operator,
            lexeme: "*" | "/" | "%",
            ..
        } => (9, 10),
        Token {
            ttype: Symbol,
            lexeme: IF_KEYWORD,
            ..
        } => (13, 14),
        Token {
            ttype: Operator,
            lexeme: ".",
            ..
        } => (15, 16),
        Token {
            ttype: LeftParen, ..
        } => (17, 18),
        Token { ttype: Symbol, .. } => (6, 5),
        _ => None?,
    }
    .into()
}
