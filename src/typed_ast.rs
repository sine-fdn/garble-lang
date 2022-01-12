use crate::ast::{Type, MetaInfo, Party, ParamDef, Op};

pub struct Program {
    pub fn_defs: Vec<FnDef>,
    pub main: MainDef,
}

pub struct FnDef {
    pub identifier: String,
    pub ty: Type,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}

pub struct MainDef {
    pub ty: Type,
    pub params: Vec<(Party, ParamDef)>,
    pub body: Expr,
    pub meta: MetaInfo,
}

pub struct Expr(pub ExprEnum, pub Type, pub MetaInfo);

pub enum ExprEnum {
    True,
    False,
    Identifier(String),
    Op(Op, Box<Expr>, Box<Expr>),
}
