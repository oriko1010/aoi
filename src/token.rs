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

impl<'a> Token<'a> {
    pub fn new(ttype: TokenType, trivia: &'a str, lexeme: &'a str) -> Self {
        Self {
            ttype,
            trivia,
            lexeme,
        }
    }
}

impl Token<'static> {
    pub const EOF: Self = Self {
        ttype: TokenType::Eof,
        trivia: "",
        lexeme: "",
    };
}
