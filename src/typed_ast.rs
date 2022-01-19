use crate::{
    ast::{Op, ParamDef, Party, Type},
    parser::MetaInfo,
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Program {
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
    Identifier(String),
    Op(Op, Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    FnCall(String, Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}
