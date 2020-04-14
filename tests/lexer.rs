use aoi::{
    lexer::Lexer,
    token::{
        Token,
        TokenType::{self, *},
    },
};

#[test]
fn all() {
    let tokens = lex("(number+-{}4)\"hello!\"");
    let expect = vec![
        tok(LeftParen, "("),
        tok(Symbol, "number"),
        tok(Operator, "+-"),
        tok(LeftBrace, "{"),
        tok(RightBrace, "}"),
        tok(Number, "4"),
        tok(RightParen, ")"),
        tok(String, "\"hello!\""),
    ];
    equals(&tokens, &expect);
}

#[test]
fn operators() {
    let tokens = lex("+/+-*{<<<");
    let expect = vec![
        tok(Operator, "+/+-*"),
        tok(LeftBrace, "{"),
        tok(Operator, "<<<"),
    ];
    equals(&tokens, &expect);
}

#[test]
fn numbers() {
    let tokens = lex("123 456 8.8.8.8");
    let expect = vec![
        tok(Number, "123"),
        tok(Number, "456"),
        tok(Number, "8.8"),
        tok(Operator, "."),
        tok(Number, "8.8"),
    ];
    equals(&tokens, &expect);
}

#[test]
fn strings() {
    let tokens = lex("\"quoted\"\"string\"");
    let expect = vec![tok(String, "\"quoted\""), tok(String, "\"string\"")];
    equals(&tokens, &expect);
}

#[test]
fn trivia() {
    let (ref x5, ref x10) = (" ".repeat(5), " ".repeat(10));
    let comment = "// comment\n";
    let code = format!("{}white{}space{}4", x10, x5, comment);
    let tokens = lex(&code);
    let expect = vec![
        tok2(Symbol, "white", x10),
        tok2(Symbol, "space", x5),
        tok2(Number, "4", comment),
    ];
    equals_trivia(&tokens, &expect);
}

fn equals(tokens: &[Token], expected: &[Token]) {
    assert_eq!(tokens.len(), expected.len());
    for (token, expect) in tokens.iter().zip(expected.iter()) {
        assert_eq!(token.ttype, expect.ttype);
        assert_eq!(token.lexeme, expect.lexeme);
    }
}

fn equals_trivia(tokens: &[Token], expected: &[Token]) {
    assert_eq!(tokens.len(), expected.len());
    for (token, expect) in tokens.iter().zip(expected.iter()) {
        assert_eq!(token.ttype, expect.ttype);
        assert_eq!(token.lexeme, expect.lexeme);
        assert_eq!(token.trivia, expect.trivia);
    }
}

fn tok(ttype: TokenType, lexeme: &str) -> Token {
    Token::new(ttype, "", lexeme)
}

fn tok2<'a>(ttype: TokenType, lexeme: &'a str, trivia: &'a str) -> Token<'a> {
    Token::new(ttype, trivia, lexeme)
}

fn lex(code: &str) -> Vec<Token> {
    let lexer = Lexer::new(code);
    let mut tokens = Vec::new();
    for token in lexer {
        tokens.push(token)
    }
    tokens
}
