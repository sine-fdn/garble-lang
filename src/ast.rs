pub struct Program {
    pub fn_defs: Vec<FnDef>,
    pub main: MainDef,
}

pub struct MetaInfo {
    //line: usize,
    //column: usize,
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

pub enum Type {
    Bool,
}

pub struct ParamDef(pub String, pub Type);

pub enum Party {
    InA,
    InB,
}

pub struct Expr(pub ExprEnum, pub MetaInfo);

pub enum ExprEnum {
    True,
    False,
    Identifier(String),
    Op(Op, Box<Expr>, Box<Expr>),
}

pub enum Op {
    BitAnd,
    BitXor,
}
