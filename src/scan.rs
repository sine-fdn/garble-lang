//! Splits a source code into a stream of [`crate::scan::Token`]s.

use std::{iter::Peekable, str::Chars};

use crate::token::{MetaInfo, SignedNumType, Token, TokenEnum, UnsignedNumType};

/// An error found during scanning, with its location in the source code.
#[derive(Debug, Clone)]
pub struct ScanError(pub ScanErrorEnum, pub MetaInfo);

/// The different kinds of errors found during scanning.
#[derive(Debug, Clone)]
pub enum ScanErrorEnum {
    /// The scanned character is not a valid token.
    UnexpectedCharacter,
    /// The scanned token is not a valid unsigned number.
    InvalidUnsignedNum,
    /// The scanned token is not a valid signed number.
    InvalidSignedNum,
}

impl std::fmt::Display for ScanErrorEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScanErrorEnum::UnexpectedCharacter => f.write_str("Unexpected character"),
            ScanErrorEnum::InvalidUnsignedNum => f.write_str("Invalid unsigned number"),
            ScanErrorEnum::InvalidSignedNum => f.write_str("Invalid signed number"),
        }
    }
}

/// A stream of tokens.
pub struct Tokens(pub Vec<Token>);

/// Splits the source code into tokens (or returns scan errors).
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
                '^' => self.push_token(TokenEnum::Caret),
                '*' => self.push_token(TokenEnum::Star),
                '+' => self.push_token(TokenEnum::Plus),
                '&' => {
                    if self.next_matches('&') {
                        self.push_token(TokenEnum::DoubleAmpersand);
                    } else {
                        self.push_token(TokenEnum::Ampersand);
                    }
                }
                '|' => {
                    if self.next_matches('|') {
                        self.push_token(TokenEnum::DoubleBar);
                    } else {
                        self.push_token(TokenEnum::Bar);
                    }
                }
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
                        while !(self.peek('\n') || self.is_empty()) {
                            self.advance();
                        }
                    } else if self.next_matches('*') {
                        let mut level = 1;
                        loop {
                            if self.next_matches('/') && self.next_matches('*') {
                                level += 1;
                            } else if self.next_matches('*') && self.next_matches('/') {
                                level -= 1;
                            } else if !self.peek('*') && !self.peek('/') {
                                self.advance();
                            }
                            if level == 0 {
                                break;
                            }
                        }
                    } else {
                        self.push_token(TokenEnum::Slash);
                    }
                }
                '-' => {
                    if self.next_matches('>') {
                        self.push_token(TokenEnum::Arrow);
                    } else {
                        let mut digits = vec!['-'];
                        while let Some(digit) = self.next_matches_digit() {
                            digits.push(digit);
                        }
                        if digits.len() == 1 {
                            self.push_token(TokenEnum::Minus);
                        } else {
                            let n: String = digits.into_iter().collect();
                            if let Ok(n) = n.parse::<i128>() {
                                let mut literal_suffix = String::new();
                                while let Some(char) = self.next_matches_alphanumeric() {
                                    literal_suffix.push(char);
                                }
                                let literal_suffix = match literal_suffix.as_str() {
                                    "" if n >= i32::MIN as i128 && n <= i32::MAX as i128 => None,
                                    "i8" if n >= i8::MIN as i128 && n <= i8::MAX as i128 => {
                                        Some(SignedNumType::I8)
                                    }
                                    "i16" if n >= i16::MIN as i128 && n <= i16::MAX as i128 => {
                                        Some(SignedNumType::I16)
                                    }
                                    "i32" if n >= i32::MIN as i128 && n <= i32::MAX as i128 => {
                                        Some(SignedNumType::I32)
                                    }
                                    "i64" if n >= i64::MIN as i128 && n <= i64::MAX as i128 => {
                                        Some(SignedNumType::I64)
                                    }
                                    "i128" => Some(SignedNumType::I128),
                                    _ => {
                                        self.push_error(ScanErrorEnum::InvalidUnsignedNum);
                                        None
                                    }
                                };
                                self.push_token(TokenEnum::SignedNum(n, literal_suffix));
                            } else {
                                self.push_error(ScanErrorEnum::InvalidSignedNum);
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
                        let n: String = digits.into_iter().collect();
                        if let Ok(n) = n.parse::<u128>() {
                            let mut literal_suffix = String::new();
                            while let Some(char) = self.next_matches_alphanumeric() {
                                literal_suffix.push(char);
                            }
                            let token = match literal_suffix.as_str() {
                                "" if n <= i32::MAX as u128 => TokenEnum::UnsignedNum(n, None),
                                "i8" if n <= i8::MAX as u128 => {
                                    TokenEnum::SignedNum(n as i128, Some(SignedNumType::I8))
                                }
                                "i16" if n <= i16::MAX as u128 => {
                                    TokenEnum::SignedNum(n as i128, Some(SignedNumType::I16))
                                }
                                "i32" if n <= i32::MAX as u128 => {
                                    TokenEnum::SignedNum(n as i128, Some(SignedNumType::I32))
                                }
                                "i64" if n <= i64::MAX as u128 => {
                                    TokenEnum::SignedNum(n as i128, Some(SignedNumType::I64))
                                }
                                "i128" if n <= i128::MAX as u128 => {
                                    TokenEnum::SignedNum(n as i128, Some(SignedNumType::I128))
                                }
                                "usize" if n <= usize::MAX as u128 => {
                                    TokenEnum::UnsignedNum(n, Some(UnsignedNumType::Usize))
                                }
                                "u8" if n <= u8::MAX as u128 => {
                                    TokenEnum::UnsignedNum(n, Some(UnsignedNumType::U8))
                                }
                                "u16" if n <= u16::MAX as u128 => {
                                    TokenEnum::UnsignedNum(n, Some(UnsignedNumType::U16))
                                }
                                "u32" if n <= u32::MAX as u128 => {
                                    TokenEnum::UnsignedNum(n, Some(UnsignedNumType::U32))
                                }
                                "u64" if n <= u64::MAX as u128 => {
                                    TokenEnum::UnsignedNum(n, Some(UnsignedNumType::U64))
                                }
                                "u128" => TokenEnum::UnsignedNum(n, Some(UnsignedNumType::U128)),
                                _ => {
                                    self.push_error(ScanErrorEnum::InvalidUnsignedNum);
                                    TokenEnum::UnsignedNum(n, None)
                                }
                            };
                            self.push_token(token);
                        } else {
                            self.push_error(ScanErrorEnum::InvalidUnsignedNum);
                        }
                    } else if is_alphanumeric(c) {
                        let mut chars = vec![c];
                        while let Some(char) = self.next_matches_alphanumeric() {
                            chars.push(char);
                        }
                        let identifier: String = chars.into_iter().collect();
                        match identifier.as_str() {
                            "struct" => self.push_token(TokenEnum::KeywordStruct),
                            "enum" => self.push_token(TokenEnum::KeywordEnum),
                            "fn" => self.push_token(TokenEnum::KeywordFn),
                            "let" => self.push_token(TokenEnum::KeywordLet),
                            "if" => self.push_token(TokenEnum::KeywordIf),
                            "else" => self.push_token(TokenEnum::KeywordElse),
                            "match" => self.push_token(TokenEnum::KeywordMatch),
                            "as" => self.push_token(TokenEnum::KeywordAs),
                            "pub" => self.push_token(TokenEnum::KeywordPub),
                            _ => self.push_token(TokenEnum::Identifier(identifier)),
                        }
                    } else {
                        self.push_error(ScanErrorEnum::UnexpectedCharacter);
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

    fn is_empty(&mut self) -> bool {
        self.chars.peek().is_none()
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
    ('0'..='9').contains(&c)
}

fn is_alphanumeric(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c) || c == '_' || is_digit(c)
}
