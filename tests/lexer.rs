use aoi::{
    lexer::Lexer,
    token::{
        Token,
        TokenType::{self, *},
    },
};

#[test]
fn tokens() {
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
fn trivia() {
    let (ref x5, ref x10) = (" ".repeat(5), " ".repeat(10));
    let code = format!("{}white{}space\n4", x10, x5);
    let tokens = lex(&code);
    let expect = vec![
        tok2(Symbol, "white", x10),
        tok2(Symbol, "space", x5),
        tok2(Number, "4", "\n"),
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
    Token {
        ttype,
        lexeme,
        trivia: "",
    }
}

fn tok2<'a>(ttype: TokenType, lexeme: &'a str, trivia: &'a str) -> Token<'a> {
    Token {
        ttype,
        lexeme,
        trivia,
    }
}

fn lex(code: &str) -> Vec<Token> {
    let lexer = Lexer::new(code);
    let mut tokens = Vec::new();
    for token in lexer {
        tokens.push(token)
    }
    tokens
}
