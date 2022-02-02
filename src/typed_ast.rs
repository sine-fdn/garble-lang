use crate::{
    ast::{EnumDef, Op, ParamDef, Party, Type, UnaryOp},
    parser::MetaInfo,
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Program {
    pub enum_defs: Vec<EnumDef>,
    pub fn_defs: Vec<FnDef>,
    pub main: MainDef,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnDef {
    pub identifier: String,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MainDef {
    pub params: Vec<(Party, ParamDef)>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Expr(pub ExprEnum, pub Type, pub MetaInfo);

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
    Match(Box<Expr>, Vec<(VariantPattern, Expr)>),
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
pub enum VariantExpr {
    Unit(String),
    Tuple(String, Vec<Expr>),
}

impl VariantExpr {
    pub fn variant_name(&self) -> &str {
        match self {
            VariantExpr::Unit(name) => name.as_str(),
            VariantExpr::Tuple(name, _) => name.as_str(),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VariantPattern {
    Unit(String),
    Tuple(String, Vec<(String, Type)>),
}

impl VariantPattern {
    pub fn variant_name(&self) -> &str {
        match self {
            VariantPattern::Unit(name) => name.as_str(),
            VariantPattern::Tuple(name, _) => name.as_str(),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Closure {
    pub ty: Type,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}
