//! The typed Abstract Syntax Tree (AST).

use std::collections::HashMap;

use crate::{
    ast::{EnumDef, Op, ParamDef, Type, UnaryOp},
    token::{MetaInfo, SignedNumType, UnsignedNumType},
};

/// A program, consisting of top level definitions (enums or functions).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    /// Top level enum type definitions.
    pub enum_defs: HashMap<String, EnumDef>,
    /// Top level function definitions.
    pub fn_defs: HashMap<String, FnDef>,
    /// The main function that will be compiled and evaluated as a circuit.
    pub main: FnDef,
}

/// A top level function definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnDef {
    /// The name of the function.
    pub identifier: String,
    /// The parameters of the function.
    pub params: Vec<ParamDef>,
    /// The body expression that the function evaluates to.
    pub body: Expr,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// An expression, its type and its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Expr(pub ExprEnum, pub Type, pub MetaInfo);

/// The different kinds of expressions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ExprEnum {
    /// Literal `true`.
    True,
    /// Literal `false`.
    False,
    /// Unsigned number literal.
    NumUnsigned(u128, Option<UnsignedNumType>),
    /// Signed number literal.
    NumSigned(i128, Option<SignedNumType>),
    /// Identifier (either a variable or a function).
    Identifier(String),
    /// Array literal which explicitly specifies all of its elements.
    ArrayLiteral(Vec<Expr>),
    /// Array "repeat expression", which specifies 1 element, to be repeated a number of times.
    ArrayRepeatLiteral(Box<Expr>, usize),
    /// Access of an array at the specified index, returning its element.
    ArrayAccess(Box<Expr>, Box<Expr>),
    /// Purely functional array update, returns a new array with the element at the index replaced.
    ArrayAssignment(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Tuple literal containing the specified fields.
    TupleLiteral(Vec<Expr>),
    /// Access of a tuple at the specified position.
    TupleAccess(Box<Expr>, usize),
    /// Enum literal of the specified variant, possibly with fields.
    EnumLiteral(String, Box<VariantExpr>),
    /// Matching the specified expression with a list of clauses (pattern + expression).
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    /// Application of a unary operator.
    UnaryOp(UnaryOp, Box<Expr>),
    /// Application of a binary operator.
    Op(Op, Box<Expr>, Box<Expr>),
    /// A block that lexically scopes any bindings introduced within it.
    LexicallyScopedBlock(Box<Expr>),
    /// Let expression, binds variables to expressions and evaluates the body with them in scope.
    Let(Vec<(String, Expr)>, Box<Expr>),
    /// Call of the specified function with a list of arguments.
    FnCall(String, Vec<Expr>),
    /// If-else expression for the specified condition, if-expr and else-expr.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Explicit cast of an expression to the specified type.
    Cast(Type, Box<Expr>),
    /// `fold`s the specified array, with the specified initial value and a 2-param closure.
    Fold(Box<Expr>, Box<Expr>, Box<Closure>),
    /// `map`s the specified array with the specified 1-param closure.
    Map(Box<Expr>, Box<Closure>),
    /// Range of numbers from the specified min (inclusive) to the specified max (exclusive).
    Range(usize, usize),
}

/// A variant literal, used by [`ExprEnum::EnumLiteral`], with type and location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct VariantExpr(pub String, pub VariantExprEnum, pub MetaInfo);

/// The different kinds of variant literals.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VariantExprEnum {
    /// A unit variant, containing no fields.
    Unit,
    /// A tuple variant, containing positional fields (but can be empty).
    Tuple(Vec<Expr>),
}

/// A (possibly nested) pattern used by [`ExprEnum::Match`], with its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Pattern(pub PatternEnum, pub Type, pub MetaInfo);

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            PatternEnum::Identifier(name) => f.write_str(name),
            PatternEnum::True => f.write_str("true"),
            PatternEnum::False => f.write_str("false"),
            PatternEnum::NumUnsigned(n) => n.fmt(f),
            PatternEnum::NumSigned(n) => n.fmt(f),
            PatternEnum::Tuple(fields) => {
                f.write_str("(")?;
                let mut fields = fields.iter();
                if let Some(field) = fields.next() {
                    field.fmt(f)?;
                }
                for field in fields {
                    f.write_str(", ")?;
                    field.fmt(f)?;
                }
                f.write_str(")")
            }
            PatternEnum::EnumUnit(enum_name, variant_name) => {
                f.write_fmt(format_args!("{enum_name}::{variant_name}"))
            }
            PatternEnum::EnumTuple(enum_name, variant_name, fields) => {
                f.write_fmt(format_args!("{enum_name}::{variant_name}("))?;
                let mut fields = fields.iter();
                if let Some(field) = fields.next() {
                    field.fmt(f)?;
                }
                for field in fields {
                    f.write_str(", ")?;
                    field.fmt(f)?;
                }
                f.write_str(")")
            }
            PatternEnum::UnsignedInclusiveRange(min, max) => {
                if min == max {
                    min.fmt(f)
                } else {
                    let max = max + 1;
                    f.write_fmt(format_args!("{min}..{max}"))
                }
            }
            PatternEnum::SignedInclusiveRange(min, max) => {
                if min == max {
                    min.fmt(f)
                } else {
                    let max = max + 1;
                    f.write_fmt(format_args!("{min}..{max}"))
                }
            }
        }
    }
}

/// The different kinds of patterns.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PatternEnum {
    /// A variable, always matches.
    Identifier(String),
    /// Matches `true`.
    True,
    /// Matches `false`.
    False,
    /// Matches the specified unsigned number.
    NumUnsigned(u128),
    /// Matches the specified signed number.
    NumSigned(i128),
    /// Matches a tuple if all of its fields match their respective patterns.
    Tuple(Vec<Pattern>),
    /// Matches an enum with the specified name and variant.
    EnumUnit(String, String),
    /// Matches an enum with the specified name and variant, if all fields match.
    EnumTuple(String, String, Vec<Pattern>),
    /// Matches any number inside the usigned range between min (inclusive) and max (inclusive).
    UnsignedInclusiveRange(u128, u128),
    /// Matches any number inside the signed range between min (inclusive) and max (inclusive).
    SignedInclusiveRange(i128, i128),
}

/// A non-first-flass closure, used only by [`ExprEnum::Map`] and [`ExprEnum::Fold`].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Closure {
    /// The return type of the closure.
    pub ty: Type,
    /// The parameters (name and type) of the closure.
    pub params: Vec<ParamDef>,
    /// The expression that the closures evaluates to.
    pub body: Expr,
    /// The location in the source code.
    pub meta: MetaInfo,
}
