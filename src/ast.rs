//! The untyped Abstract Syntax Tree (AST).

use std::hash::Hash;
use std::{collections::HashMap, fmt::Display};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{
    token::{MetaInfo, SignedNumType, UnsignedNumType},
    UntypedExpr,
};

/// A program, consisting of top level definitions (enums or functions).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Program<T> {
    /// The external constants that the top level const definitions depend upon.
    pub const_deps: HashMap<String, HashMap<String, (T, MetaInfo)>>,
    /// Top level const definitions.
    pub const_defs: HashMap<String, ConstDef>,
    /// Top level struct type definitions.
    pub struct_defs: HashMap<String, StructDef>,
    /// Top level enum type definitions.
    pub enum_defs: HashMap<String, EnumDef>,
    /// Top level function definitions.
    pub fn_defs: HashMap<String, FnDef<T>>,
}

/// A top level const definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ConstDef {
    /// The type of the constant.
    pub ty: Type,
    /// The value of the constant.
    pub value: ConstExpr,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// A constant value, either a literal, a namespaced symbol or an aggregate.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ConstExpr(pub ConstExprEnum, pub MetaInfo);

impl Display for ConstExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

// Impl hash consistent with PartialEq which ignores metainfo
impl Hash for ConstExpr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl PartialEq for ConstExpr {
    fn eq(&self, other: &Self) -> bool {
        // Ignore MetaInfo for equality to enable typ-checking of join
        self.0 == other.0
    }
}

impl Eq for ConstExpr {}

/// The different kinds of constant expressions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ConstExprEnum {
    /// Boolean `true`.
    True,
    /// Boolean `false`.
    False,
    /// Unsigned integer.
    NumUnsigned(u64, UnsignedNumType),
    /// Signed integer.
    NumSigned(i64, SignedNumType),
    /// An external value supplied before compilation.
    ExternalValue {
        /// The party providing the value.
        party: String,
        /// The variable name of the value.
        identifier: String,
    },
    /// Identifier of another const expr
    ConstExprIdent(String),
    /// The maximum of several constant expressions.
    Max(Vec<ConstExpr>),
    /// The minimum of several constant expressions.
    Min(Vec<ConstExpr>),
    /// The sum of several constant expressions.
    Add(Box<ConstExpr>, Box<ConstExpr>),
    /// The first constant expression minus the second one.
    Sub(Box<ConstExpr>, Box<ConstExpr>),
}

impl Display for ConstExprEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstExprEnum::True => f.write_str("true"),
            ConstExprEnum::False => f.write_str("false"),
            ConstExprEnum::NumUnsigned(n, unsigned_num_type) => {
                if let UnsignedNumType::Unspecified = unsigned_num_type {
                    write!(f, "{n}")
                } else {
                    write!(f, "{n}{unsigned_num_type}")
                }
            }
            ConstExprEnum::NumSigned(n, signed_num_type) => {
                if let SignedNumType::Unspecified = signed_num_type {
                    write!(f, "{n}")
                } else {
                    write!(f, "{n}{signed_num_type}")
                }
            }
            ConstExprEnum::ExternalValue { party, identifier } => {
                write!(f, "{party}::{identifier}")
            }
            ConstExprEnum::ConstExprIdent(ident) => f.write_str(ident),
            ConstExprEnum::Max(const_exprs) | ConstExprEnum::Min(const_exprs) => {
                if let ConstExprEnum::Max(_) = self {
                    f.write_str("max(")?;
                } else {
                    f.write_str("min(")?;
                }
                let args: Vec<_> = const_exprs.iter().map(|arg| arg.to_string()).collect();
                let args: String = args.join(", ");
                write!(f, "{args})")
            }
            ConstExprEnum::Add(l, r) => {
                write!(f, "{l} + {r}")
            }
            ConstExprEnum::Sub(l, r) => {
                write!(f, "{l} - {r}")
            }
        }
    }
}

/// A top level struct type definition.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StructDef {
    /// The variants of the enum type.
    pub fields: Vec<(String, Type)>,
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

impl EnumDef {
    pub(crate) fn get_variant(&self, variant_name: &str) -> Option<&Variant> {
        self.variants
            .iter()
            .find(|&variant| variant.variant_name() == variant_name)
    }
}

/// An enum variant.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FnDef<T> {
    /// Whether or not the function is public.
    pub is_pub: bool,
    /// The name of the function.
    pub identifier: String,
    /// The return type of the function.
    pub ty: Type,
    /// The parameters of the function.
    pub params: Vec<ParamDef>,
    /// The body expression that the function evaluates to.
    pub body: Vec<Stmt<T>>,
    /// The location in the source code.
    pub meta: MetaInfo,
}

/// A parameter definition (mutability flag, parameter name and type).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ParamDef {
    /// Indicates whether the parameters was declared to be mutable or immutable.
    pub mutability: Mutability,
    /// The identifier of the parameter.
    pub name: String,
    /// The type of the parameter.
    pub ty: Type,
}

/// Indicates whether a variable is declared as mutable.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Mutability {
    /// The variable is declared as mutable.
    Mutable,
    /// The variable is declared as immutable.
    Immutable,
}

impl From<bool> for Mutability {
    fn from(b: bool) -> Self {
        if b {
            Mutability::Mutable
        } else {
            Mutability::Immutable
        }
    }
}

/// Either a concrete type or a struct/enum that needs to be looked up in the definitions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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
    /// Array type of a fixed size, with the size specified by a constant.
    ArrayConst(Box<Type>, String),
    /// Array type of a fixed size, with the size specified by a constant expression.
    ArrayConstExpr(Box<Type>, ConstExpr),
    /// Tuple type containing fields of the specified types.
    Tuple(Vec<Type>),
    /// A struct or an enum, depending on the top level definitions (used only before typechecking).
    UntypedTopLevelDefinition(String, MetaInfo),
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
            Type::ArrayConst(ty, size) => {
                f.write_str("[")?;
                ty.fmt(f)?;
                f.write_str("; ")?;
                size.fmt(f)?;
                f.write_str("]")
            }
            Type::ArrayConstExpr(ty, size_expr) => {
                f.write_str("[")?;
                ty.fmt(f)?;
                f.write_str("; ")?;
                size_expr.fmt(f)?;
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
            Type::UntypedTopLevelDefinition(name, _) => f.write_str(name),
            Type::Struct(name) => f.write_str(name),
            Type::Enum(name) => f.write_str(name),
        }
    }
}

/// A statement and its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Stmt<T> {
    /// The kind of statement being wrapped.
    pub inner: StmtEnum<T>,
    /// Metadata indicating the location of the statement in the source code.
    pub meta: MetaInfo,
}

impl<T> Stmt<T> {
    /// Creates a new statement with the given metadata.
    pub fn new(inner: StmtEnum<T>, meta: MetaInfo) -> Self {
        Self { inner, meta }
    }
}

/// The different kinds of statements.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum StmtEnum<T> {
    /// Let expression, binds variables to exprs.
    Let(Pattern<T>, Option<Type>, Expr<T>),
    /// Mutable let expression, bind a single variable to an expr.
    LetMut(String, Option<Type>, Expr<T>),
    /// Assignment of a (previously as mutable declared) variable.
    VarAssign(String, Vec<(Accessor<T>, MetaInfo)>, Expr<T>),
    /// Binds an identifier to each value of an array expr, evaluating the body.
    ForEachLoop(Pattern<T>, Expr<T>, Vec<Stmt<T>>),
    /// Binds an identifier to each joined row of two tables, evaluating the body.
    JoinLoop(Pattern<T>, T, (Expr<T>, Expr<T>), Vec<Stmt<T>>),
    /// An expression (all expressions are statements, but not all statements expressions).
    Expr(Expr<T>),
}

/// The different ways a mutable variable can be accessed before assignment.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Accessor<T> {
    /// Accessing an array by index to assign to it, e.g. `array[0] = x;`.
    ArrayAccess {
        /// The type of the array being accessed by the index.
        array_ty: T,
        /// The expression that indexes the array.
        index: Expr<T>,
    },
    /// Accessing a tuple field by index to assign to it, e.g. `tuple.0 = x;`.
    TupleAccess {
        /// The type of the tuple being accessed by the index.
        tuple_ty: T,
        /// The index of the field of the tuple.
        index: usize,
    },
    /// Accessing a struct field by index to assign to it, e.g. `struct.foo = x;`.
    StructAccess {
        /// The type of the struct being accessed by the field.
        struct_ty: T,
        /// The name of the field of the struct.
        field: String,
    },
}

/// An expression and its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Expr<T> {
    /// The kind of expression being wrapped.
    pub inner: ExprEnum<T>,
    /// Metadata indicating the location of the expression in the source code.
    pub meta: MetaInfo,
    /// The type of the expression.
    pub ty: T,
}

impl Expr<()> {
    /// Constructs an expression without any associated type information.
    pub fn untyped(expr: ExprEnum<()>, meta: MetaInfo) -> Self {
        Self {
            inner: expr,
            meta,
            ty: (),
        }
    }
}

impl Expr<Type> {
    /// Constructs an expression with an associated type.
    pub fn typed(expr: ExprEnum<Type>, ty: Type, meta: MetaInfo) -> Self {
        Self {
            inner: expr,
            meta,
            ty,
        }
    }
}

/// Function calls to built-in functions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum BuiltInFnCall<T> {
    /// Built-in bitonic sorting-based join function.
    Join {
        /// The type of the element that is joined on.
        join_ty: T,
        /// False if we do a simple set intersection and true if we join
        /// on the first element of tuple and have associated data with
        /// each entry. Is set during type checking.
        has_assoc_data: bool,
        /// The arguments to join.
        args: Vec<Expr<T>>,
    },
}

impl BuiltInFnCall<()> {
    /// Try to construct an [`BuiltInFnCall`] from an ident and args.
    ///
    /// Returns the args if the ident matches no built-in fn.
    pub fn try_from_ident_args(
        ident: &str,
        args: Vec<UntypedExpr>,
    ) -> Result<Self, Vec<UntypedExpr>> {
        let has_assoc_data = false;
        match ident {
            "join" => Ok(Self::Join {
                join_ty: (),
                has_assoc_data,
                args,
            }),
            _ => Err(args),
        }
    }
}

/// The different kinds of expressions.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ExprEnum<T> {
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
    ArrayLiteral(Vec<Expr<T>>),
    /// Array "repeat expression", which specifies 1 element, to be repeated a number of times.
    ArrayRepeatLiteral(Box<Expr<T>>, usize),
    /// Array "repeat expression", with the size specified by a constant.
    ArrayRepeatLiteralConst(Box<Expr<T>>, String),
    /// Access of an array at the specified index, returning its element.
    ArrayAccess(Box<Expr<T>>, Box<Expr<T>>),
    /// Tuple literal containing the specified fields.
    TupleLiteral(Vec<Expr<T>>),
    /// Access of a tuple at the specified position.
    TupleAccess(Box<Expr<T>>, usize),
    /// Access of a struct at the specified field.
    StructAccess(Box<Expr<T>>, String),
    /// Struct literal with the specified fields.
    StructLiteral(String, Vec<(String, Expr<T>)>),
    /// Enum literal of the specified variant, possibly with fields.
    EnumLiteral(String, String, VariantExprEnum<T>),
    /// Matching the specified expression with a list of clauses (pattern + expression).
    Match(Box<Expr<T>>, Vec<(Pattern<T>, Expr<T>)>),
    /// Application of a unary operator.
    UnaryOp(UnaryOp, Box<Expr<T>>),
    /// Application of a binary operator.
    Op(Op, Box<Expr<T>>, Box<Expr<T>>),
    /// A block that lexically scopes any bindings introduced within it.
    Block(Vec<Stmt<T>>),
    /// Call of the specified function with a list of arguments.
    FnCall(String, Vec<Expr<T>>),
    /// A call to an built-in, potentially generic function.
    BuiltInFnCall(BuiltInFnCall<T>),
    /// If-else expression for the specified condition, if-expr and else-expr.
    If(Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
    /// Explicit cast of an expression to the specified type.
    Cast(Type, Box<Expr<T>>),
    /// Range of numbers from the specified min (inclusive) to the specified max (exclusive).
    Range(u64, u64, UnsignedNumType),
}

/// The different kinds of variant literals.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum VariantExprEnum<T> {
    /// A unit variant, containing no fields.
    Unit,
    /// A tuple variant, containing positional fields (but can be empty).
    Tuple(Vec<Expr<T>>),
}

/// A (possibly nested) pattern used by [`ExprEnum::Match`], with its location in the source code.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Pattern<T>(pub PatternEnum<T>, pub MetaInfo, pub T);

impl Pattern<()> {
    /// Constructs a pattern without any associated type information.
    pub fn untyped(pattern: PatternEnum<()>, meta: MetaInfo) -> Self {
        Self(pattern, meta, ())
    }
}

impl Pattern<Type> {
    /// Constructs a pattern with an associated type.
    pub fn typed(pattern: PatternEnum<Type>, ty: Type, meta: MetaInfo) -> Self {
        Self(pattern, meta, ty)
    }
}

/// The different kinds of patterns.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum PatternEnum<T> {
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
    Tuple(Vec<Pattern<T>>),
    /// Matches a struct if all of its fields match their respective patterns.
    Struct(String, Vec<(String, Pattern<T>)>),
    /// Matches a struct if its fields match their respective patterns, ignoring remaining fields.
    StructIgnoreRemaining(String, Vec<(String, Pattern<T>)>),
    /// Matches an enum with the specified name and variant.
    EnumUnit(String, String),
    /// Matches an enum with the specified name and variant, if all fields match.
    EnumTuple(String, String, Vec<Pattern<T>>),
    /// Matches any number inside the unsigned range between min (inclusive) and max (inclusive).
    UnsignedInclusiveRange(u64, u64, UnsignedNumType),
    /// Matches any number inside the signed range between min (inclusive) and max (inclusive).
    SignedInclusiveRange(i64, i64, SignedNumType),
}

impl<T> std::fmt::Display for Pattern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            PatternEnum::Identifier(name) => f.write_str(name),
            PatternEnum::True => f.write_str("true"),
            PatternEnum::False => f.write_str("false"),
            PatternEnum::NumUnsigned(n, suffix) => f.write_fmt(format_args!("{n}{suffix}")),
            PatternEnum::NumSigned(n, suffix) => f.write_fmt(format_args!("{n}{suffix}")),
            PatternEnum::Struct(struct_name, fields) => {
                f.write_fmt(format_args!("{struct_name} {{ "))?;
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
            PatternEnum::StructIgnoreRemaining(struct_name, fields) => {
                f.write_fmt(format_args!("{struct_name} {{ "))?;
                for (field_name, field) in fields.iter() {
                    f.write_fmt(format_args!("{field_name}: {field}"))?;
                    f.write_str(", ")?;
                }
                f.write_str(".. }")
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
            PatternEnum::UnsignedInclusiveRange(min, max, suffix) => {
                if min == max {
                    f.write_fmt(format_args!("{min}{suffix}"))
                } else if *min == 0 && Some(*max) == suffix.max() {
                    f.write_str("_")
                } else {
                    f.write_fmt(format_args!("{min}{suffix}..={max}{suffix}"))
                }
            }
            PatternEnum::SignedInclusiveRange(min, max, suffix) => {
                if min == max {
                    f.write_fmt(format_args!("{min}{suffix}"))
                } else if Some(*min) == suffix.min() && Some(*max) == suffix.max() {
                    f.write_str("_")
                } else {
                    f.write_fmt(format_args!("{min}{suffix}..={max}{suffix}"))
                }
            }
        }
    }
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
