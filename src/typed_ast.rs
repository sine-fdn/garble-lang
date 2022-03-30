//! The typed Abstract Syntax Tree (AST).

use std::collections::HashMap;

use crate::{
    ast::{Op, UnaryOp},
    token::{MetaInfo, SignedNumType, UnsignedNumType},
};

/// A program, consisting of top level definitions (enums or functions).
#[derive(Debug, Clone, PartialEq, Eq)]
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
pub struct StructDef {
    /// The variants of the enum type.
    pub fields: Vec<(String, Type)>,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// A top level enum type definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct EnumDef {
    /// The variants of the enum type.
    pub variants: Vec<Variant>,
    /// The location in the source code.
    pub meta: MetaInfo,
}

impl EnumDef {
    pub(crate) fn get_variant(&self, variant_name: &str) -> Option<&Variant> {
        for variant in self.variants.iter() {
            if variant.variant_name() == variant_name {
                return Some(variant);
            }
        }
        None
    }
}

/// An enum variant.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Variant {
    /// A unit variant with the specified name, but containing no fields.
    Unit(String),
    /// A tuple variant with the specified name, containing positional fields.
    Tuple(String, Vec<Type>),
}

impl Variant {
    pub(crate) fn variant_name(&self) -> &str {
        match self {
            Variant::Unit(name) => name.as_str(),
            Variant::Tuple(name, _) => name.as_str(),
        }
    }

    pub(crate) fn types(&self) -> Option<Vec<Type>> {
        match self {
            Variant::Unit(_) => None,
            Variant::Tuple(_, types) => Some(types.clone()),
        }
    }
}

/// A top level function definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnDef {
    /// Whether or not the function is public.
    pub is_pub: bool,
    /// The name of the function.
    pub identifier: String,
    /// The parameters of the function.
    pub params: Vec<ParamDef>,
    /// The body expression that the function evaluates to.
    pub body: Expr,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// A parameter definition (parameter name and type).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ParamDef(pub String, pub Type);

/// A type, can be either explicitly specified or inferred by the type checker.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type {
    /// Boolean type with the values true and false.
    Bool,
    /// Unsigned number types
    Unsigned(UnsignedNumType),
    /// Signed number types
    Signed(SignedNumType),
    /// Function type with the specified parameters and the specified return type.
    Fn(Vec<Type>, Box<Type>),
    /// Array type of a fixed size, containing elements of the specified type.
    Array(Box<Type>, usize),
    /// Tuple type containing fields of the specified types.
    Tuple(Vec<Type>),
    /// Struct type of the specified name, needs to be looked up in struct defs for its field types.
    Struct(String),
    /// Enum type of the specified name, needs to be looked up in enum defs for its variant types.
    Enum(String),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Bool => f.write_str("bool"),
            Type::Unsigned(n) => n.fmt(f),
            Type::Signed(n) => n.fmt(f),
            Type::Fn(params, ret_ty) => {
                f.write_str("(")?;
                let mut params = params.iter();
                if let Some(param) = params.next() {
                    param.fmt(f)?;
                }
                for param in params {
                    f.write_str(", ")?;
                    param.fmt(f)?;
                }
                f.write_str(") -> ")?;
                ret_ty.fmt(f)
            }
            Type::Array(ty, size) => {
                f.write_str("[")?;
                ty.fmt(f)?;
                f.write_str("; ")?;
                size.fmt(f)?;
                f.write_str("]")
            }
            Type::Tuple(fields) => {
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
            Type::Struct(name) => f.write_str(name),
            Type::Enum(name) => f.write_str(name),
        }
    }
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
    LexicallyScopedBlock(Box<Expr>),
    /// Let expression, binds variables to expressions and evaluates the body with them in scope.
    Let(Vec<(Pattern, Expr)>, Box<Expr>),
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
            PatternEnum::Struct(struct_name, fields) => {
                f.write_fmt(format_args!("{struct_name} {{"))?;
                let mut fields = fields.iter();
                if let Some((field_name, field)) = fields.next() {
                    f.write_fmt(format_args!("{field_name}: {field}"))?;
                }
                for (field_name, field) in fields {
                    f.write_str(", ")?;
                    f.write_fmt(format_args!("{field_name}: {field}"))?;
                }
                f.write_str("}")
            }
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
                    match self.1 {
                        Type::Unsigned(n) if *min == 0 && *max == n.max() => f.write_str("_"),
                        _ => {
                            let max = max + 1;
                            f.write_fmt(format_args!("{min}..{max}"))
                        }
                    }
                }
            }
            PatternEnum::SignedInclusiveRange(min, max) => {
                if min == max {
                    min.fmt(f)
                } else {
                    match self.1 {
                        Type::Signed(n) if *min == n.min() && *max == n.max() => f.write_str("_"),
                        _ => {
                            let max = max + 1;
                            f.write_fmt(format_args!("{min}..{max}"))
                        }
                    }
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
    /// Matches a struct if all of its fields math their respective patterns.
    Struct(String, Vec<(String, Pattern)>),
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
