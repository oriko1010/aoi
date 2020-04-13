#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TokenType {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Symbol,
    Operator,
    Number,
    String,
    Error,
    Eof,
}

#[derive(Debug)]
pub struct Token<'a> {
    pub ttype: TokenType,
    pub trivia: &'a str,
    pub lexeme: &'a str,
}
