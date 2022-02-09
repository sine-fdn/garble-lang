use std::{iter::Peekable, str::Chars};

use crate::token::{MetaInfo, Token, TokenEnum};


#[derive(Debug, Clone)]
pub struct ScanError(pub ScanErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum ScanErrorEnum {
    UnexpectedCharacter(char),
    InvalidUnsignedNum(String),
    InvalidSignedNum(String),
}


pub struct Tokens(pub Vec<Token>);

pub fn scan(prg: &str) -> Result<Tokens, Vec<ScanError>> {
    let tokens = Scanner::new(prg).scan()?;
    Ok(Tokens(tokens))
}

struct Scanner<'a> {
    tokens: Vec<Token>,
    errors: Vec<ScanError>,
    chars: Peekable<Chars<'a>>,
    line: usize,
    column: usize,
    current_token_start: (usize, usize),
}

impl<'a> Scanner<'a> {
    fn new(prg: &'a str) -> Self {
        Self {
            tokens: vec![],
            errors: vec![],
            chars: prg.chars().peekable(),
            line: 0,
            column: 0,
            current_token_start: (0, 0),
        }
    }

    fn scan(mut self) -> Result<Vec<Token>, Vec<ScanError>> {
        while let Some(char) = self.chars.next() {
            match char {
                ' ' | '\r' | '\t' => {
                    self.current_token_start = (self.line, self.column);
                }
                '\n' => {
                    self.line += 1;
                    self.column = 0;
                }
                '(' => self.push_token(TokenEnum::LeftParen),
                ')' => self.push_token(TokenEnum::RightParen),
                '{' => self.push_token(TokenEnum::LeftBrace),
                '}' => self.push_token(TokenEnum::RightBrace),
                '[' => self.push_token(TokenEnum::LeftBracket),
                ']' => self.push_token(TokenEnum::RightBracket),
                '.' => self.push_token(TokenEnum::Dot),
                ',' => self.push_token(TokenEnum::Comma),
                ';' => self.push_token(TokenEnum::Semicolon),
                '%' => self.push_token(TokenEnum::Percent),
                '&' => self.push_token(TokenEnum::Ampersand),
                '|' => self.push_token(TokenEnum::Bar),
                '^' => self.push_token(TokenEnum::Caret),
                '*' => self.push_token(TokenEnum::Star),
                '+' => self.push_token(TokenEnum::Plus),
                '!' => {
                    if self.next_matches('=') {
                        self.push_token(TokenEnum::BangEq);
                    } else {
                        self.push_token(TokenEnum::Bang);
                    }
                }
                '=' => {
                    if self.next_matches('=') {
                        self.push_token(TokenEnum::DoubleEq);
                    } else if self.next_matches('>') {
                        self.push_token(TokenEnum::FatArrow);
                    } else {
                        self.push_token(TokenEnum::Eq);
                    }
                }
                ':' => {
                    if self.next_matches(':') {
                        self.push_token(TokenEnum::DoubleColon);
                    } else {
                        self.push_token(TokenEnum::Colon);
                    }
                }
                '>' => {
                    if self.next_matches('>') {
                        self.push_token(TokenEnum::DoubleGreaterThan);
                    } else {
                        self.push_token(TokenEnum::GreaterThan);
                    }
                }
                '<' => {
                    if self.next_matches('<') {
                        self.push_token(TokenEnum::DoubleLessThan);
                    } else {
                        self.push_token(TokenEnum::LessThan);
                    }
                }
                '/' => {
                    if self.next_matches('/') {
                        while !self.peek('\n') {
                            self.advance();
                        }
                    } else {
                        self.push_token(TokenEnum::Slash);
                    }
                }
                '-' => {
                    if self.next_matches('>') {
                        self.push_token(TokenEnum::Arrow);
                    } else {
                        let mut digits = vec![];
                        while let Some(digit) = self.next_matches_digit() {
                            digits.push(digit);
                        }
                        if digits.is_empty() {
                            self.push_token(TokenEnum::Minus);
                        } else {
                            let n: String = digits.into_iter().collect();
                            if let Ok(n) = n.parse::<i128>() {
                                self.push_token(TokenEnum::SignedNum(n));
                            } else {
                                self.push_error(ScanErrorEnum::InvalidSignedNum(n));
                            }
                        }
                    }
                }
                c => {
                    if is_digit(c) {
                        let mut digits = vec![c];
                        while let Some(digit) = self.next_matches_digit() {
                            digits.push(digit);
                        }
                        if digits.is_empty() {
                            self.push_token(TokenEnum::Minus);
                        } else {
                            let n: String = digits.into_iter().collect();
                            if let Ok(n) = n.parse::<u128>() {
                                self.push_token(TokenEnum::UnsignedNum(n));
                            } else {
                                self.push_error(ScanErrorEnum::InvalidUnsignedNum(n));
                            }
                        }
                    } else if is_alphanumeric(c) {
                        let mut chars = vec![c];
                        while let Some(char) = self.next_matches_alphanumeric() {
                            chars.push(char);
                        }
                        let identifier: String = chars.into_iter().collect();
                        match identifier.as_str() {
                            "fn" => self.push_token(TokenEnum::KeywordFn),
                            _ => self.push_token(TokenEnum::Identifier(identifier)),
                        }
                    } else {
                        self.push_error(ScanErrorEnum::UnexpectedCharacter(c));
                    }
                }
            }
            self.column += 1;
        }

        if self.errors.is_empty() {
            Ok(self.tokens)
        } else {
            Err(self.errors)
        }
    }

    fn next_matches_alphanumeric(&mut self) -> Option<char> {
        if let Some(c) = self.chars.peek().copied() {
            if is_alphanumeric(c) {
                self.advance();
                return Some(c);
            }
        }
        None
    }

    fn next_matches_digit(&mut self) -> Option<char> {
        if let Some(c) = self.chars.peek().copied() {
            if is_digit(c) {
                self.advance();
                return Some(c);
            }
        }
        None
    }

    fn next_matches(&mut self, c: char) -> bool {
        if self.peek(c) {
            self.advance();
            return true;
        }
        false
    }

    fn peek(&mut self, c: char) -> bool {
        if let Some(next_char) = self.chars.peek() {
            return *next_char == c;
        }
        false
    }

    fn advance(&mut self) {
        self.column += 1;
        self.chars.next();
    }

    fn push_token(&mut self, t: TokenEnum) {
        if self.current_token_start == (self.line, self.column) {
            self.column += 1;
        }
        let current_token_end = (self.line, self.column);
        let meta = MetaInfo {
            start: self.current_token_start,
            end: current_token_end,
        };
        self.current_token_start = current_token_end;
        self.tokens.push(Token(t, meta));
    }

    fn push_error(&mut self, err: ScanErrorEnum) {
        let meta = MetaInfo {
            start: (self.line, self.column),
            end: (self.line, self.column),
        };
        self.errors.push(ScanError(err, meta));
    }
}

fn is_digit(c: char) -> bool {
    c >= '0' && c <= '9'
}

fn is_alphanumeric(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || is_digit(c)
}
