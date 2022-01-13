use crate::ast::{Type, MetaInfo, Party, ParamDef, Op};

#[derive(Debug, Clone)]
pub struct Program {
    pub fn_defs: Vec<FnDef>,
    pub main: MainDef,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub identifier: String,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone)]
pub struct MainDef {
    pub params: Vec<(Party, ParamDef)>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone)]
pub struct Expr(pub ExprEnum, pub Type, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum ExprEnum {
    True,
    False,
    NumU8(u8),
    Identifier(String),
    Op(Op, Box<Expr>, Box<Expr>),
}
