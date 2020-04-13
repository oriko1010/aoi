use crate::{
    ast::*,
    lexer::Lexer,
    token::{Token, TokenType},
};
use anyhow::{anyhow, bail, ensure, Result};
use std::iter::Peekable;

pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
    current: Token<'a>,
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
            current: Token {
                ttype: TokenType::Error,
                lexeme: "",
                trivia: "",
            },
        }
    }

    pub fn parse_program(&mut self) -> Result<Program> {
        let mut expressions = Vec::with_capacity(32);
        loop {
            match self.parse_primary() {
                Ok(expression) => expressions.push(expression),
                Err(e) => {
                    eprintln!("{}", e);
                    break;
                }
            }
        }
        Ok(Program { expressions })
    }

    fn parse_expression(&mut self) -> Result<Expression> {
        let primary = self.parse_primary()?;
        Ok(primary)
    }

    fn parse_primary(&mut self) -> Result<Expression> {
        use TokenType::*;

        let token = self.peek_token()?;
        match token {
            Token {
                ttype: Symbol,
                lexeme: LET_KEYWORD,
                ..
            } => self.parse_assign().map(Into::into),
            Token {
                ttype: Symbol,
                lexeme: FUN_KEYWORD,
                ..
            } => self.parse_function().map(Into::into),
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
            Token { ttype: Symbol, .. } => {
                let identifier = self.parse_identifier()?;
                if self.peek_matches(TokenType::LeftParen, "(") {
                    self.parse_call(identifier, None).map(Into::into)
                } else if self.peek_matches(TokenType::Operator, ".") {
                    self.expect(TokenType::Operator, ".")?;
                    let member = self.parse_identifier()?;
                    let call = self.parse_call(member, Some(identifier))?;
                    Ok(call.into())
                } else {
                    Ok(identifier.into())
                }
            }
            Token { ttype: Number, .. } => self.parse_integer().map(Into::into),
            Token { ttype: String, .. } => self.parse_string().map(Into::into),
            Token {
                ttype: LeftParen, ..
            } => self.parse_grouping(),
            Token {
                ttype: LeftBrace, ..
            } => self.parse_block().map(Into::into),
            Token {
                ttype: Operator, ..
            } => self.parse_binary_op().map(Into::into),
            _ => bail!("Unexpected {:?} in primary expression.", token),
        }
    }

    fn parse_grouping(&mut self) -> Result<Expression> {
        self.expect(TokenType::LeftParen, "(")?;
        let expression = self.parse_expression()?;
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
                let expression = self.parse_expression()?;
                expressions.push(expression);
            }
        }
    }

    fn parse_binary_op(&mut self) -> Result<BinaryOp> {
        let op = self.parse_operator()?.to_owned();
        let lhs = self.parse_expression()?;
        let rhs = self.parse_expression()?;
        Ok(BinaryOp::new(lhs, &op, rhs))
    }

    fn parse_integer(&mut self) -> Result<Integer> {
        let lexeme = self.next_token()?.lexeme;
        let value = lexeme
            .parse::<u64>()
            .map_err(|_| anyhow!("Error parsing integer literal"))?;
        Ok(Integer::from(value))
    }

    fn parse_string(&mut self) -> Result<String> {
        let lexeme = self.next_token()?.lexeme;
        ensure!(
            lexeme.starts_with('"') && lexeme.ends_with('"'),
            "Error parsing string literal"
        );
        Ok(String::new(&lexeme[1..lexeme.len() - 1]))
    }

    fn parse_identifier(&mut self) -> Result<Identifier> {
        let lexeme = self.next_token()?.lexeme;
        Ok(Identifier::from(lexeme))
    }

    fn parse_bool(&mut self) -> Result<Bool> {
        let lexeme = self.next_token()?.lexeme;
        match lexeme {
            TRUE_KEYWORD => Ok(Bool::new(true)),
            FALSE_KEYWORD => Ok(Bool::new(false)),
            _ => bail!("Error parsing boolean"),
        }
    }

    fn parse_operator(&mut self) -> Result<&str> {
        match self.next_token() {
            Ok(Token {
                ttype: TokenType::Operator,
                lexeme,
                ..
            }) => Ok(*lexeme),
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
            let body = self.parse_expression()?;
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
        let condition = self.parse_expression()?;
        let then = self.parse_expression()?;
        let other = if self.peek_matches(TokenType::Symbol, ELSE_KEYWORD) {
            self.expect(TokenType::Symbol, ELSE_KEYWORD)?;
            Some(self.parse_expression()?)
        } else {
            None
        };
        Ok(If::new(condition, then, other))
    }

    fn parse_assign(&mut self) -> Result<Assign> {
        self.expect_symbol(LET_KEYWORD)?;
        let identifier = self.parse_identifier()?;
        self.expect_operator("=")?;
        let expression = self.parse_expression()?;
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

    fn parse_call(&mut self, identifier: Identifier, first: Option<Identifier>) -> Result<Call> {
        let mut arguments = Vec::new();
        if let Some(first) = first {
            arguments.push(first.into());
        }

        self.expect(TokenType::LeftParen, "(")?;
        loop {
            if self.peek_matches(TokenType::RightParen, ")") {
                self.expect(TokenType::RightParen, ")")?;
                break Ok(Call::new(identifier, arguments));
            } else {
                let argument = self.parse_expression()?;
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

    fn next_token(&mut self) -> Result<&Token> {
        let token = self.lexer.next().ok_or(anyhow!("No more tokens."))?;
        self.current = token;
        Ok(&self.current)
    }

    fn peek_token(&mut self) -> Result<&Token> {
        let token = self.lexer.peek().ok_or(anyhow!("No more tokens."))?;
        Ok(token)
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

    fn expect(&mut self, ttype: TokenType, lexeme: &str) -> Result<&Token> {
        let next = self.next_token()?;
        if next.ttype != ttype {
            bail!("Expected token type {:?}, found {:?}", ttype, next.ttype);
        }
        if next.lexeme != lexeme {
            bail!(
                "Expected token lexeme {:?}, found {:?}",
                lexeme,
                next.lexeme
            );
        }
        Ok(&next)
    }

    #[inline]
    fn expect_symbol(&mut self, lexeme: &str) -> Result<&Token> {
        self.expect(TokenType::Symbol, lexeme)
    }

    #[inline]
    fn expect_operator(&mut self, lexeme: &str) -> Result<&Token> {
        self.expect(TokenType::Operator, lexeme)
    }
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum Precedence {
    None,
    Assign,
    Equality,
    Comparison,
    Add,
    Multiply,
}

impl Precedence {
    fn of(token: &Token) -> Precedence {
        use Precedence::*;
        assert_eq!(token.ttype, TokenType::Operator);
        match token.lexeme {
            "=" => Assign,
            "==" | "!=" => Equality,
            ">" | "<" | ">=" | "<=" => Comparison,
            "+" | "-" => Add,
            "*" | "/" | "%" => Multiply,
            _ => None,
        }
    }

    fn next(self) -> Precedence {
        use Precedence::*;
        match self {
            None => Assign,
            Assign => Equality,
            Equality => Comparison,
            Comparison => Add,
            Add => Multiply,
            Multiply => None,
        }
    }
}
