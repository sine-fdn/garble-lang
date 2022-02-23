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
    UnsignedNum(u128, Option<UnsignedNumType>),
    /// Signed number.
    SignedNum(i128, Option<SignedNumType>),
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

/// A suffix indicating the explicit unsigned number type of the literal.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum UnsignedNumType {
    /// Unsigned integer type used to index arrays, length depends on the host platform.
    Usize,
    /// 8-bit unsigned integer type.
    U8,
    /// 16-bit unsigned integer type.
    U16,
    /// 32-bit unsigned integer type.
    U32,
    /// 64-bit unsigned integer type.
    U64,
    /// 128-bit unsigned integer type.
    U128,
}

/// A suffix indicating the explicit signed number type of the literal.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum SignedNumType {
    /// 8-bit signed integer type.
    I8,
    /// 16-bit signed integer type.
    I16,
    /// 32-bit signed integer type.
    I32,
    /// 64-bit signed integer type.
    I64,
    /// 128-bit signed integer type.
    I128,
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
