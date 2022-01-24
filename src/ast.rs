use crate::parser::MetaInfo;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Program {
    pub fn_defs: Vec<FnDef>,
    pub main: MainDef,
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
    Fn(Vec<Type>, Box<Type>)
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ParamDef(pub String, pub Type);

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Party {
    A,
    B,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Expr(pub ExprEnum, pub MetaInfo);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ExprEnum {
    True,
    False,
    NumUnsigned(u128),
    NumSigned(i128),
    Identifier(String),
    UnaryOp(UnaryOp, Box<Expr>),
    Op(Op, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    FnCall(String, Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Cast(Type, Box<Expr>),
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
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
