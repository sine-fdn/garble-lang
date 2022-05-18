//! The untyped Abstract Syntax Tree (AST).

use std::collections::HashMap;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::token::{MetaInfo, SignedNumType, UnsignedNumType};

/// A program, consisting of top level definitions (enums or functions).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Program {
    /// Top level struct type definitions.
    pub struct_defs: HashMap<String, StructDef>,
    /// Top level enum type definitions.
    pub enum_defs: HashMap<String, EnumDef>,
    /// Top level function definitions.
    pub fn_defs: HashMap<String, FnDef>,
}

/// A top level struct type definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StructDef {
    /// The variants of the enum type.
    pub fields: Vec<(String, PreliminaryType)>,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// A top level enum type definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct EnumDef {
    /// The variants of the enum type.
    pub variants: Vec<Variant>,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// An enum variant.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Variant {
    /// A unit variant with the specified name, but containing no fields.
    Unit(String),
    /// A tuple variant with the specified name, containing positional fields.
    Tuple(String, Vec<PreliminaryType>),
}

/// A top level function definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FnDef {
    /// Whether or not the function is public.
    pub is_pub: bool,
    /// The name of the function.
    pub identifier: String,
    /// The return type of the function.
    pub ty: PreliminaryType,
    /// The parameters of the function.
    pub params: Vec<ParamDef>,
    /// The body expression that the function evaluates to.
    pub body: Vec<Stmt>,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// A parameter definition (mutability flag, parameter name and type).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ParamDef(pub bool, pub String, pub PreliminaryType);

/// Either a concrete type or a struct/enum that needs to be looked up in the definitions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum PreliminaryType {
    /// Boolean type with the values true and false.
    Bool,
    /// Unsigned number types
    Unsigned(UnsignedNumType),
    /// Signed number types
    Signed(SignedNumType),
    /// Function type with the specified parameters and the specified return type.
    Fn(Vec<PreliminaryType>, Box<PreliminaryType>),
    /// Array type of a fixed size, containing elements of the specified type.
    Array(Box<PreliminaryType>, usize),
    /// Tuple type containing fields of the specified types.
    Tuple(Vec<PreliminaryType>),
    /// A struct or an enum, depending on the top level definitions.
    StructOrEnum(String, MetaInfo),
}

/// A statement and its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Stmt(pub StmtEnum, pub MetaInfo);

/// The different kinds of statements.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum StmtEnum {
    /// Let expression, binds variables to exprs.
    Let(Pattern, Expr),
    /// Mutable let expression, bind a single variable to an expr.
    LetMut(String, Expr),
    /// Assignment of a (previously as mutable declared) variable.
    VarAssign(String, Expr),
    /// Assignment of an index in a (mutable) array.
    ArrayAssign(String, Expr, Expr),
    /// Binds an identifier to each value of an array expr, evaluating the body.
    ForEachLoop(String, Expr, Vec<Stmt>),
    /// An expression (all expressions are statements, but not all statements expressions).
    Expr(Expr),
}

/// An expression and its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Expr(pub ExprEnum, pub MetaInfo);

/// The different kinds of expressions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ExprEnum {
    /// Literal `true`.
    True,
    /// Literal `false`.
    False,
    /// Unsigned number literal.
    NumUnsigned(u64, UnsignedNumType),
    /// Signed number literal.
    NumSigned(i64, SignedNumType),
    /// Identifier (either a variable or a function).
    Identifier(String),
    /// Array literal which explicitly specifies all of its elements.
    ArrayLiteral(Vec<Expr>),
    /// Array "repeat expression", which specifies 1 element, to be repeated a number of times.
    ArrayRepeatLiteral(Box<Expr>, usize),
    /// Access of an array at the specified index, returning its element.
    ArrayAccess(Box<Expr>, Box<Expr>),
    /// Tuple literal containing the specified fields.
    TupleLiteral(Vec<Expr>),
    /// Access of a tuple at the specified position.
    TupleAccess(Box<Expr>, usize),
    /// Access of a struct at the specified field.
    StructAccess(Box<Expr>, String),
    /// Struct literal with the specified fields.
    StructLiteral(String, Vec<(String, Expr)>),
    /// Enum literal of the specified variant, possibly with fields.
    EnumLiteral(String, Box<VariantExpr>),
    /// Matching the specified expression with a list of clauses (pattern + expression).
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    /// Application of a unary operator.
    UnaryOp(UnaryOp, Box<Expr>),
    /// Application of a binary operator.
    Op(Op, Box<Expr>, Box<Expr>),
    /// A block that lexically scopes any bindings introduced within it.
    Block(Vec<Stmt>),
    /// Call of the specified function with a list of arguments.
    FnCall(String, Vec<Expr>),
    /// If-else expression for the specified condition, if-expr and else-expr.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Explicit cast of an expression to the specified type.
    Cast(PreliminaryType, Box<Expr>),
    /// Range of numbers from the specified min (inclusive) to the specified max (exclusive).
    Range((u64, UnsignedNumType), (u64, UnsignedNumType)),
}

/// A variant literal, used by [`ExprEnum::EnumLiteral`], with its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct VariantExpr(pub String, pub VariantExprEnum, pub MetaInfo);

/// The different kinds of variant literals.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum VariantExprEnum {
    /// A unit variant, containing no fields.
    Unit,
    /// A tuple variant, containing positional fields (but can be empty).
    Tuple(Vec<Expr>),
}

/// A (possibly nested) pattern used by [`ExprEnum::Match`], with its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Pattern(pub PatternEnum, pub MetaInfo);

/// The different kinds of patterns.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum PatternEnum {
    /// A variable, always matches.
    Identifier(String),
    /// Matches `true`.
    True,
    /// Matches `false`.
    False,
    /// Matches the specified unsigned number.
    NumUnsigned(u64, UnsignedNumType),
    /// Matches the specified signed number.
    NumSigned(i64, SignedNumType),
    /// Matches a tuple if all of its fields match their respective patterns.
    Tuple(Vec<Pattern>),
    /// Matches a struct if all of its fields match their respective patterns.
    Struct(String, Vec<(String, Pattern)>),
    /// Matches a struct if its fields match their respective patterns, ignoring remaining fields.
    StructIgnoreRemaining(String, Vec<(String, Pattern)>),
    /// Matches an enum with the specified name and variant.
    EnumUnit(String, String),
    /// Matches an enum with the specified name and variant, if all fields match.
    EnumTuple(String, String, Vec<Pattern>),
    /// Matches any number inside the unsigned range between min (inclusive) and max (inclusive).
    UnsignedInclusiveRange(u64, u64, UnsignedNumType),
    /// Matches any number inside the signed range between min (inclusive) and max (inclusive).
    SignedInclusiveRange(i64, i64, SignedNumType),
}

/// The different kinds of unary operator.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum UnaryOp {
    /// Bitwise / logical negation (`!`).
    Not,
    /// Arithmetic negation (`-`).
    Neg,
}

/// the different kinds of binary operators.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Op {
    /// Addition (`+`).
    Add,
    /// Subtraction (`-`).
    Sub,
    /// Multiplication (`*`).
    Mul,
    /// Division (`/`).
    Div,
    /// Modulo (`%`).
    Mod,
    /// Bitwise and (`&`).
    BitAnd,
    /// Bitwise xor (`^`).
    BitXor,
    /// Bitwise or (`|`).
    BitOr,
    /// Greater-than (`>`).
    GreaterThan,
    /// Less-than (`<`).
    LessThan,
    /// Equals (`==`).
    Eq,
    /// Not-equals (`!=`).
    NotEq,
    /// Bitwise shift-left (`<<`).
    ShiftLeft,
    /// Bitwise shift-right (`>>`).
    ShiftRight,
    /// Short-circuiting and (`&&`).
    ShortCircuitAnd,
    /// Short-circuiting or (`||`).
    ShortCircuitOr,
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Add => f.write_str("+"),
            Op::Sub => f.write_str("-"),
            Op::Mul => f.write_str("*"),
            Op::Div => f.write_str("/"),
            Op::Mod => f.write_str("%"),
            Op::BitAnd => f.write_str("&"),
            Op::BitXor => f.write_str("^"),
            Op::BitOr => f.write_str("|"),
            Op::GreaterThan => f.write_str(">"),
            Op::LessThan => f.write_str("<"),
            Op::Eq => f.write_str("=="),
            Op::NotEq => f.write_str("!="),
            Op::ShiftLeft => f.write_str("<<"),
            Op::ShiftRight => f.write_str(">>"),
            Op::ShortCircuitAnd => f.write_str("&&"),
            Op::ShortCircuitOr => f.write_str("||"),
        }
    }
}
