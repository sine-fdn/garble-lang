//! Tokens produced by [`crate::scan::scan`].

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Tokens produced by [`crate::scan::scan`].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Token(pub TokenEnum, pub MetaInfo);

/// The different kinds of tokens.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TokenEnum {
    /// Identifier of alphanumeric chars.
    Identifier(String),
    /// Constant unsigned number used to index arrays / tuples.
    ConstantIndexOrSize(u32),
    /// Unsigned number.
    UnsignedNum(u128, UnsignedNumType),
    /// Signed number.
    SignedNum(i128, SignedNumType),
    /// `enum` keyword.
    KeywordEnum,
    /// `struct` keyword.
    KeywordStruct,
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
    /// `mut` keyword.
    KeywordMut,
    /// `as` keyword.
    KeywordAs,
    /// `pub` keyword.
    KeywordPub,
    /// `for` keyword.
    KeywordFor,
    /// `in` keyword.
    KeywordIn,
    /// `.`.
    Dot,
    /// `..`.
    DoubleDot,
    /// `..=`.
    DoubleDotEquals,
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
    /// `&&`.
    DoubleAmpersand,
    /// `|`.
    Bar,
    /// `||`.
    DoubleBar,
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

impl std::fmt::Display for TokenEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenEnum::Identifier(s) => f.write_str(s),
            TokenEnum::ConstantIndexOrSize(num) => f.write_fmt(format_args!("{num}")),
            TokenEnum::UnsignedNum(num, suffix) => f.write_fmt(format_args!("{num}{suffix}")),
            TokenEnum::SignedNum(num, suffix) => f.write_fmt(format_args!("{num}{suffix}")),
            TokenEnum::KeywordStruct => f.write_str("struct"),
            TokenEnum::KeywordEnum => f.write_str("enum"),
            TokenEnum::KeywordFn => f.write_str("fn"),
            TokenEnum::KeywordLet => f.write_str("let"),
            TokenEnum::KeywordIf => f.write_str("if"),
            TokenEnum::KeywordElse => f.write_str("else"),
            TokenEnum::KeywordMut => f.write_str("mut"),
            TokenEnum::KeywordMatch => f.write_str("match"),
            TokenEnum::KeywordAs => f.write_str("as"),
            TokenEnum::KeywordPub => f.write_str("pub"),
            TokenEnum::KeywordFor => f.write_str("for"),
            TokenEnum::KeywordIn => f.write_str("in"),
            TokenEnum::Dot => f.write_str("."),
            TokenEnum::DoubleDot => f.write_str(".."),
            TokenEnum::DoubleDotEquals => f.write_str("..="),
            TokenEnum::Comma => f.write_str(","),
            TokenEnum::Semicolon => f.write_str(";"),
            TokenEnum::Colon => f.write_str(":"),
            TokenEnum::DoubleColon => f.write_str("::"),
            TokenEnum::Arrow => f.write_str("->"),
            TokenEnum::FatArrow => f.write_str("=>"),
            TokenEnum::LeftParen => f.write_str("("),
            TokenEnum::RightParen => f.write_str(")"),
            TokenEnum::LeftBrace => f.write_str("{"),
            TokenEnum::RightBrace => f.write_str("}"),
            TokenEnum::LeftBracket => f.write_str("["),
            TokenEnum::RightBracket => f.write_str("]"),
            TokenEnum::Plus => f.write_str("+"),
            TokenEnum::Minus => f.write_str("-"),
            TokenEnum::Slash => f.write_str("/"),
            TokenEnum::Star => f.write_str("*"),
            TokenEnum::Percent => f.write_str("%"),
            TokenEnum::Ampersand => f.write_str("&"),
            TokenEnum::DoubleAmpersand => f.write_str("&&"),
            TokenEnum::Bar => f.write_str("|"),
            TokenEnum::DoubleBar => f.write_str("||"),
            TokenEnum::Caret => f.write_str("^"),
            TokenEnum::Bang => f.write_str("!"),
            TokenEnum::Eq => f.write_str("="),
            TokenEnum::DoubleEq => f.write_str("=="),
            TokenEnum::BangEq => f.write_str("!="),
            TokenEnum::GreaterThan => f.write_str(">"),
            TokenEnum::LessThan => f.write_str("<"),
            TokenEnum::DoubleGreaterThan => f.write_str(">>"),
            TokenEnum::DoubleLessThan => f.write_str("<<"),
        }
    }
}

/// A suffix indicating the explicit unsigned number type of the literal.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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

impl UnsignedNumType {
    /// Returns the max value representable by this type.
    pub fn max(&self) -> u128 {
        match self {
            UnsignedNumType::Usize => u32::MAX as u128,
            UnsignedNumType::U8 => u8::MAX as u128,
            UnsignedNumType::U16 => u16::MAX as u128,
            UnsignedNumType::U32 => u32::MAX as u128,
            UnsignedNumType::U64 => u64::MAX as u128,
            UnsignedNumType::U128 => u128::MAX as u128,
        }
    }
}

impl std::fmt::Display for UnsignedNumType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            UnsignedNumType::Usize => "usize",
            UnsignedNumType::U8 => "u8",
            UnsignedNumType::U16 => "u16",
            UnsignedNumType::U32 => "u32",
            UnsignedNumType::U64 => "u64",
            UnsignedNumType::U128 => "u128",
        })
    }
}

/// A suffix indicating the explicit signed number type of the literal.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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

impl SignedNumType {
    /// Returns the minimum value representable by this type.
    pub fn min(&self) -> i128 {
        match self {
            SignedNumType::I8 => i8::MIN as i128,
            SignedNumType::I16 => i16::MIN as i128,
            SignedNumType::I32 => i32::MIN as i128,
            SignedNumType::I64 => i64::MIN as i128,
            SignedNumType::I128 => i128::MIN as i128,
        }
    }

    /// Returns the maximum value representable by this type.
    pub fn max(&self) -> i128 {
        match self {
            SignedNumType::I8 => i8::MAX as i128,
            SignedNumType::I16 => i16::MAX as i128,
            SignedNumType::I32 => i32::MAX as i128,
            SignedNumType::I64 => i64::MAX as i128,
            SignedNumType::I128 => i128::MAX as i128,
        }
    }
}

impl std::fmt::Display for SignedNumType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            SignedNumType::I8 => "i8",
            SignedNumType::I16 => "i16",
            SignedNumType::I32 => "i32",
            SignedNumType::I64 => "i64",
            SignedNumType::I128 => "i128",
        })
    }
}

/// The location of a token in the source code, from start `(line, column)` to end `(line, column)`.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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

impl PartialOrd for MetaInfo {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.start.partial_cmp(&other.start) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.end.partial_cmp(&other.end)
    }
}

impl Ord for MetaInfo {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.start.cmp(&other.start) {
            core::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        self.end.cmp(&other.end)
    }
}
