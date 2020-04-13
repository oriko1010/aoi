use crate::token::{Token, TokenType};
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

    pub fn next(&mut self) -> Option<Token<'a>> {
        let current = loop {
            match self.chars.peek() {
                Some((_, ' ' | '\n')) => {
                    self.chars.next();
                }
                Some(&(current, _)) => break Some(current),
                None => break None,
            }
        }?;

        let trivia = &self.code[self.position..current];
        self.position = current;

        let (current, ttype) = {
            let (current, ch) = self.chars.next()?;
            match ch {
                '{' => {
                    let next = self.chars.peek()?.0;
                    Some((next, TokenType::LeftBrace))
                }
                '}' => {
                    let next = self.chars.peek()?.0;
                    Some((next, TokenType::RightBrace))
                }
                '(' => {
                    let next = self.chars.peek()?.0;
                    Some((next, TokenType::LeftParen))
                }
                ')' => {
                    let next = self.chars.peek()?.0;
                    Some((next, TokenType::RightParen))
                }
                '"' => loop {
                    match self.chars.next() {
                        Some((current, '"')) => break Some((current + 1, TokenType::String)),
                        Some(_) => continue,
                        None => break None,
                    }
                },
                'a'..='z' | 'A'..='Z' | '_' => loop {
                    match self.chars.peek() {
                        Some((_, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_')) => {
                            self.chars.next();
                        }
                        Some(&(current, _)) => break Some((current, TokenType::Symbol)),
                        None => break Some((self.code.len(), TokenType::Symbol)),
                    }
                },
                '=' | '+' | '-' | '*' | '/' | '%' | ';' | ',' | '.' | '<' | '>' | '[' | ']' => {
                    loop {
                        match self.chars.peek() {
                            Some((
                                _,
                                '=' | '+' | '-' | '*' | '/' | '%' | ';' | ',' | '.' | '<' | '>'
                                | '[' | ']',
                            )) => {
                                self.chars.next();
                            }
                            Some(&(current, _)) => break Some((current, TokenType::Operator)),
                            None => break Some((self.code.len(), TokenType::Operator)),
                        }
                    }
                }
                '0'..='9' => loop {
                    match self.chars.peek() {
                        Some((_, '0'..='9')) => {
                            self.chars.next();
                        }
                        Some(&(current, _)) => break Some((current, TokenType::Number)),
                        None => break Some((self.code.len(), TokenType::Number)),
                    }
                },
                _ => {
                    self.chars.next();
                    Some((current, TokenType::Error))
                }
            }
        }?;

        let lexeme = &self.code[self.position..current];
        self.position = current;

        Some(Token {
            ttype,
            trivia,
            lexeme,
        })
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next()
    }
}
