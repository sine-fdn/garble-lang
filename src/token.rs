#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Token(pub TokenEnum, pub MetaInfo);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TokenEnum {
    Identifier(String),
    UnsignedNum(u128),
    SignedNum(i128),
    KeywordEnum,
    KeywordFn,
    KeywordLet,
    KeywordIf,
    KeywordElse,
    KeywordMatch,
    KeywordAs,
    Dot,
    Comma,
    Semicolon,
    Colon,
    DoubleColon,
    Arrow,
    FatArrow,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Plus,
    Minus,
    Slash,
    Star,
    Percent,
    Ampersand,
    Bar,
    Caret,
    Bang,
    Eq,
    DoubleEq,
    BangEq,
    GreaterThan,
    LessThan,
    DoubleGreaterThan,
    DoubleLessThan,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct MetaInfo {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

impl std::fmt::Debug for MetaInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(
            format!(
                "{}:{}-{}:{}",
                self.start.0, self.start.1, self.end.0, self.end.1
            )
            .as_str(),
        )
    }
}
