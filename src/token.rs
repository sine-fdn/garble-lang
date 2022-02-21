//! Tokens produced by [`crate::scan::scan`].

/// Tokens produced by [`crate::scan::scan`].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Token(pub TokenEnum, pub MetaInfo);

/// The different kinds of tokens.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TokenEnum {
    /// Identifier of alphanumeric chars.
    Identifier(String),
    /// Usigned number.
    UnsignedNum(u128),
    /// Signed number.
    SignedNum(i128),
    /// `enum` keyword.
    KeywordEnum,
    /// `fn` keyword.
    KeywordFn,
    /// `let` keyword.
    KeywordLet,
    /// `if` keyword.
    KeywordIf,
    /// `else` keyword.
    KeywordElse,
    /// `match` keyword.
    KeywordMatch,
    /// `as` keyword.
    KeywordAs,
    /// `.`.
    Dot,
    /// `,`.
    Comma,
    /// `;`.
    Semicolon,
    /// `:`.
    Colon,
    /// `::`.
    DoubleColon,
    /// `->`.
    Arrow,
    /// `=>`.
    FatArrow,
    /// `(`.
    LeftParen,
    /// `)`.
    RightParen,
    /// `{`.
    LeftBrace,
    /// `}`.
    RightBrace,
    /// `[`.
    LeftBracket,
    /// `]`.
    RightBracket,
    /// `+`.
    Plus,
    /// `-`.
    Minus,
    /// `/`.
    Slash,
    /// `*`.
    Star,
    /// `%`.
    Percent,
    /// `&`.
    Ampersand,
    /// `|`.
    Bar,
    /// `^`.
    Caret,
    /// `!`.
    Bang,
    /// `=`.
    Eq,
    /// `==`.
    DoubleEq,
    /// `!=`.
    BangEq,
    /// `>`.
    GreaterThan,
    /// `<`.
    LessThan,
    /// `>>`.
    DoubleGreaterThan,
    /// `<<`.
    DoubleLessThan,
}

/// The location of a token in the source code, from start `(line, column)` to end `(line, column)`.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct MetaInfo {
    /// The line and column of the start of the token.
    pub start: (usize, usize),
    /// The line and column of the end of the token.
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
