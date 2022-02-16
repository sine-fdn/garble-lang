use std::collections::HashMap;

use crate::{token::MetaInfo, circuit::Party};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub enum_defs: HashMap<String, EnumDef>,
    pub fn_defs: HashMap<String, FnDef>,
    pub main: MainDef,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct EnumDef {
    pub identifier: String,
    pub variants: Vec<Variant>,
    pub meta: MetaInfo,
}

impl EnumDef {
    pub fn get_variant(&self, variant_name: &str) -> Option<&Variant> {
        for variant in self.variants.iter() {
            if variant.variant_name() == variant_name {
                return Some(variant);
            }
        }
        None
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Variant {
    Unit(String),
    Tuple(String, Vec<Type>),
}

impl Variant {
    pub fn variant_name(&self) -> &str {
        match self {
            Variant::Unit(name) => name.as_str(),
            Variant::Tuple(name, _) => name.as_str(),
        }
    }

    pub fn types(&self) -> Option<Vec<Type>> {
        match self {
            Variant::Unit(_) => None,
            Variant::Tuple(_, types) => Some(types.clone()),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnDef {
    pub identifier: String,
    pub ty: Type,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MainDef {
    pub ty: Type,
    pub params: Vec<(Party, ParamDef)>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type {
    Bool,
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Fn(Vec<Type>, Box<Type>),
    Array(Box<Type>, usize),
    Tuple(Vec<Type>),
    Enum(String),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ParamDef(pub String, pub Type);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Expr(pub ExprEnum, pub MetaInfo);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ExprEnum {
    True,
    False,
    NumUnsigned(u128),
    NumSigned(i128),
    Identifier(String),
    ArrayLiteral(Box<Expr>, usize),
    ArrayAccess(Box<Expr>, Box<Expr>),
    ArrayAssignment(Box<Expr>, Box<Expr>, Box<Expr>),
    TupleLiteral(Vec<Expr>),
    TupleAccess(Box<Expr>, usize),
    EnumLiteral(String, Box<VariantExpr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    UnaryOp(UnaryOp, Box<Expr>),
    Op(Op, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    FnCall(String, Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Cast(Type, Box<Expr>),
    Fold(Box<Expr>, Box<Expr>, Box<Closure>),
    Map(Box<Expr>, Box<Closure>),
    Range(usize, usize),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct VariantExpr(pub String, pub VariantExprEnum, pub MetaInfo);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VariantExprEnum {
    Unit,
    Tuple(Vec<Expr>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Pattern(pub PatternEnum, pub MetaInfo);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PatternEnum {
    Identifier(String),
    True,
    False,
    NumUnsigned(u128),
    NumSigned(i128),
    Tuple(Vec<Pattern>),
    EnumUnit(String, String),
    EnumTuple(String, String, Vec<Pattern>),
    UnsignedInclusiveRange(u128, u128),
    SignedInclusiveRange(i128, i128),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Closure {
    pub ty: Type,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitXor,
    BitOr,
    GreaterThan,
    LessThan,
    Eq,
    NotEq,
    ShiftLeft,
    ShiftRight,
}
