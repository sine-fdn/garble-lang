use std::collections::HashMap;

use crate::{
    ast::{Expr, ExprEnum, MainDef, MetaInfo, Op, ParamDef, Party, Program, Type},
    typed_ast,
};

#[derive(Debug, Clone)]
pub struct TypeError(pub TypeErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum TypeErrorEnum {
    MaxNumSizeExceeded(Type, u64),
    ExpectedNumTypeButFound(Type),
}

impl Program {
    pub fn type_check(&self) -> Result<typed_ast::Program, TypeError> {
        let mut bindings = HashMap::new();
        let mut params = Vec::with_capacity(self.main.params.len());
        for (party, param) in self.main.params.iter() {
            let ParamDef(identifier, ty) = param;
            bindings.insert(identifier.clone(), *ty);
            params.push((*party, param.clone()));
        }
        let mut env = bindings.into();
        let body = self.main.body.type_check(&mut env, self.main.ty)?;
        let main = typed_ast::MainDef {
            params,
            body,
            meta: self.main.meta,
        };
        Ok(typed_ast::Program {
            fn_defs: vec![], // TODO
            main,
        })
    }
}

fn ensure_num_type(ty: Type, meta: MetaInfo) -> Result<Type, TypeError> {
    match ty {
        Type::Bool => Err(TypeError(TypeErrorEnum::ExpectedNumTypeButFound(ty), meta)),
        Type::U8 => Ok(Type::U8),
    }
}

impl Expr {
    fn type_check(&self, env: &mut Env, expected: Type) -> Result<typed_ast::Expr, TypeError> {
        let Expr(expr, meta) = self;
        let meta = *meta;
        let (expr, ty) = match expr {
            ExprEnum::True => (typed_ast::ExprEnum::True, Type::Bool),
            ExprEnum::False => (typed_ast::ExprEnum::False, Type::Bool),
            ExprEnum::Number(n) => {
                let expected = ensure_num_type(expected, meta)?;
                match expected {
                    Type::Bool => unreachable!("Bool cannot be the type of a number literal"),
                    Type::U8 => {
                        if *n <= u8::MAX as u64 {
                            (typed_ast::ExprEnum::NumU8(*n as u8), Type::U8)
                        } else {
                            let e = TypeErrorEnum::MaxNumSizeExceeded(Type::U8, *n);
                            return Err(TypeError(e, meta));
                        }
                    }
                }
            }
            ExprEnum::Identifier(s) => (typed_ast::ExprEnum::Identifier(s.clone()), env.get(s)),
            ExprEnum::Op(op, x, y) => match op {
                Op::Add => {
                    let expected = ensure_num_type(expected, meta)?;
                    let x = x.type_check(env, expected)?;
                    let y = y.type_check(env, expected)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        expected,
                    )
                }
                Op::BitAnd | Op::BitXor => {
                    let x = x.type_check(env, Type::Bool)?;
                    let y = y.type_check(env, Type::Bool)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        expected,
                    )
                }
            },
        };
        Ok(typed_ast::Expr(expr, ty, meta))
    }
}

type Bindings = HashMap<String, Type>;

struct Env(Vec<Bindings>);

impl Into<Env> for Bindings {
    fn into(self) -> Env {
        Env(vec![self])
    }
}

impl Env {
    fn get(&self, identifier: &str) -> Type {
        for bindings in self.0.iter().rev() {
            if let Some(ty) = bindings.get(identifier) {
                return ty.clone();
            }
        }
        panic!("Found identifier without binding: '{}'", identifier);
    }
}

#[test]
fn type_check_xor() -> Result<(), TypeError> {
    let prg = Program {
        fn_defs: vec![],
        main: MainDef {
            params: vec![(Party::A, ParamDef("x".to_string(), Type::Bool))],
            body: Expr(
                ExprEnum::Op(
                    Op::BitXor,
                    Box::new(Expr(ExprEnum::Identifier("x".to_string()), MetaInfo {})),
                    Box::new(Expr(ExprEnum::True, MetaInfo {})),
                ),
                MetaInfo {},
            ),
            ty: Type::Bool,
            meta: MetaInfo {},
        },
    };
    let typed = prg.type_check()?;
    let expected = typed_ast::Program {
        fn_defs: vec![],
        main: typed_ast::MainDef {
            params: vec![(Party::A, ParamDef("x".to_string(), Type::Bool))],
            body: typed_ast::Expr(
                typed_ast::ExprEnum::Op(
                    Op::BitXor,
                    Box::new(typed_ast::Expr(
                        typed_ast::ExprEnum::Identifier("x".to_string()),
                        Type::Bool,
                        MetaInfo {},
                    )),
                    Box::new(typed_ast::Expr(
                        typed_ast::ExprEnum::True,
                        Type::Bool,
                        MetaInfo {},
                    )),
                ),
                Type::Bool,
                MetaInfo {},
            ),
            meta: MetaInfo {},
        },
    };
    assert_eq!(typed, expected);
    Ok(())
}

#[test]
fn type_check_add() -> Result<(), TypeError> {
    let prg = Program {
        fn_defs: vec![],
        main: MainDef {
            params: vec![(Party::A, ParamDef("x".to_string(), Type::U8))],
            ty: Type::U8,
            body: Expr(
                ExprEnum::Op(
                    Op::Add,
                    Box::new(Expr(
                        ExprEnum::Identifier("x".to_string()),
                        MetaInfo {},
                    )),
                    Box::new(Expr(ExprEnum::Number(255), MetaInfo {})),
                ),
                MetaInfo {},
            ),
            meta: MetaInfo {},
        },
    };
    let typed = prg.type_check()?;
    let expected = typed_ast::Program {
        fn_defs: vec![],
        main: typed_ast::MainDef {
            params: vec![(Party::A, ParamDef("x".to_string(), Type::U8))],
            body: typed_ast::Expr(
                typed_ast::ExprEnum::Op(
                    Op::Add,
                    Box::new(typed_ast::Expr(
                        typed_ast::ExprEnum::Identifier("x".to_string()),
                        Type::U8,
                        MetaInfo {},
                    )),
                    Box::new(typed_ast::Expr(
                        typed_ast::ExprEnum::NumU8(255),
                        Type::U8,
                        MetaInfo {},
                    )),
                ),
                Type::U8,
                MetaInfo {},
            ),
            meta: MetaInfo {},
        },
    };
    assert_eq!(typed, expected);
    Ok(())
}
