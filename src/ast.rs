#[derive(Debug, Clone)]
pub struct Program {
    pub fn_defs: Vec<FnDef>,
    pub main: MainDef,
}

#[derive(Debug, Clone)]
pub struct MetaInfo {
    //line: usize,
    //column: usize,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub identifier: String,
    pub ty: Type,
    pub params: Vec<ParamDef>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone)]
pub struct MainDef {
    pub ty: Type,
    pub params: Vec<(Party, ParamDef)>,
    pub body: Expr,
    pub meta: MetaInfo,
}

#[derive(Debug, Clone)]
pub enum Type {
    Bool,
    U8,
}

#[derive(Debug, Clone)]
pub struct ParamDef(pub String, pub Type);

#[derive(Debug, Copy, Clone)]
pub enum Party {
    A,
    B,
}

#[derive(Debug, Clone)]
pub struct Expr(pub ExprEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum ExprEnum {
    True,
    False,
    Number(u64),
    Identifier(String),
    Op(Op, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Copy, Clone)]
pub enum Op {
    Add,
    BitAnd,
    BitXor,
}
