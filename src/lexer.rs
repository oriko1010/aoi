use crate::token::{Token, TokenType::*};
use std::{iter::Peekable, str::CharIndices};

pub struct Lexer<'a> {
    code: &'a str,
    position: usize,
    chars: Peekable<CharIndices<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        Self {
            code,
            position: 0,
            chars: code.char_indices().peekable(),
        }
    }

    fn next_token(&mut self) -> Token<'a> {
        let mut in_comment = false;
        let current = loop {
            match self.chars.peek() {
                Some((_, '\n')) if in_comment => {
                    self.chars.next();
                    in_comment = false;
                }
                Some((_, ' ' | '\n')) => {
                    self.chars.next();
                }
                Some(&(current, '/')) if !in_comment => {
                    let mut clone = self.chars.clone();
                    clone.next();
                    match clone.peek() {
                        Some((_, '/')) => {
                            in_comment = true;
                            continue;
                        }
                        _ => break current,
                    }
                }
                Some(_) if in_comment => {
                    self.chars.next();
                }
                Some(&(current, _)) => break current,
                None => return Token::EOF,
            }
        };

        let trivia = &self.code[self.position..current];
        self.position = current;

        let (current, ttype) = {
            let (current, ch) = match self.chars.next() {
                Some((current, ch)) => (current, ch),
                None => return Token::EOF,
            };

            match ch {
                '{' => (current + 1, LeftBrace),
                '}' => (current + 1, RightBrace),
                '(' => (current + 1, LeftParen),
                ')' => (current + 1, RightParen),
                '"' => loop {
                    match self.chars.next() {
                        Some((current, '"')) => break (current + 1, String),
                        Some(_) => continue,
                        None => break (self.code.len(), Error),
                    }
                },
                'a'..='z' | 'A'..='Z' | '_' => loop {
                    match self.chars.peek() {
                        Some((_, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_')) => {
                            self.chars.next();
                        }
                        Some(&(current, _)) => break (current, Symbol),
                        None => break (self.code.len(), Symbol),
                    }
                },
                '=' | '+' | '-' | '*' | '/' | '%' | ';' | ',' | '.' | '<' | '>' | '[' | ']'
                | '!' => loop {
                    match self.chars.peek() {
                        Some((
                            _,
                            '=' | '+' | '-' | '*' | '/' | '%' | ';' | ',' | '.' | '<' | '>' | '['
                            | ']' | '!',
                        )) => {
                            self.chars.next();
                        }
                        Some(&(current, _)) => break (current, Operator),
                        None => break (self.code.len(), Operator),
                    }
                },
                '0'..='9' => {
                    let mut has_decimal = false;
                    loop {
                        match self.chars.peek() {
                            Some((_, '0'..='9')) => {
                                self.chars.next();
                            }
                            Some(&(current, '.')) if !has_decimal => {
                                let mut clone = self.chars.clone();
                                clone.next();
                                match clone.peek() {
                                    Some((_, '0'..='9')) => {
                                        has_decimal = true;
                                        self.chars.next();
                                        continue;
                                    }
                                    _ => break (current, Number),
                                }
                            }
                            Some(&(current, _)) => break (current, Number),
                            None => break (self.code.len(), Number),
                        }
                    }
                }
                _ => {
                    self.chars.next();
                    (current, Error)
                }
            }
        };

        let lexeme = &self.code[self.position..current];
        self.position = current;

        Token::new(ttype, trivia, lexeme)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            Token { ttype: Error, .. } => None,
            Token { ttype: Eof, .. } => None,
            token => Some(token),
        }
    }
}
