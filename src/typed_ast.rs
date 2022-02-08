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
pub struct Pattern(pub PatternEnum, pub Type, pub MetaInfo);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PatternEnum {
    Identifier(String),
    True,
    False,
    NumUnsigned(u128),
    NumSigned(i128),
    Tuple(Vec<Pattern>),
    EnumUnit(String),
    EnumTuple(String, Vec<Pattern>),
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
