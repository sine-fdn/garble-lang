use std::collections::HashMap;

use crate::{
    ast::{Expr, ExprEnum, MainDef, Op, ParamDef, Party, Program, Type},
    parser::MetaInfo,
    typed_ast, env::Env,
};

#[derive(Debug, Clone)]
pub struct TypeError(pub TypeErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum TypeErrorEnum {
    IdentifierWithoutBinding(String),
    MaxNumUnsignedSizeExceeded(Type, u128),
    UnexpectedType { expected: Type, actual: Type },
    TypeMismatch((Type, MetaInfo), (Type, MetaInfo)),
}

impl Program {
    pub fn type_check(&self) -> Result<typed_ast::Program, TypeError> {
        let mut env = Env::new();
        let mut params = Vec::with_capacity(self.main.params.len());
        for (party, param) in self.main.params.iter() {
            let ParamDef(identifier, ty) = param;
            env.set(identifier.clone(), *ty);
            params.push((*party, param.clone()));
        }
        let body = self.main.body.type_check(&mut env)?;
        expect_type(&body, self.main.ty)?;
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

fn expect_type(expr: &typed_ast::Expr, expected: Type) -> Result<(), TypeError> {
    let typed_ast::Expr(_expr, actual, meta) = expr;
    let actual = *actual;
    if actual == expected {
        Ok(())
    } else {
        let e = TypeErrorEnum::UnexpectedType { expected, actual };
        Err(TypeError(e, *meta))
    }
}

fn unify(e1: &typed_ast::Expr, e2: &typed_ast::Expr, m: MetaInfo) -> Result<Type, TypeError> {
    let typed_ast::Expr(expr1, ty1, meta1) = e1;
    let typed_ast::Expr(expr2, ty2, meta2) = e2;
    match (expr1, expr2) {
        (typed_ast::ExprEnum::NumUnsigned(n1), typed_ast::ExprEnum::NumUnsigned(n2)) => {
            let n = if n1 > n2 { n1 } else { n2 };
            return Ok(min_unsigned_type(*n));
        }
        (typed_ast::ExprEnum::NumUnsigned(n), _) => {
            if is_coercible(*n, *ty2) {
                return Ok(*ty2);
            }
        }
        (_, typed_ast::ExprEnum::NumUnsigned(n)) => {
            if is_coercible(*n, *ty1) {
                return Ok(*ty1);
            }
        }
        _ => {
            if *ty1 == *ty2 {
                return Ok(*ty1);
            }
        }
    }
    let e = TypeErrorEnum::TypeMismatch((*ty1, *meta1), (*ty2, *meta2));
    Err(TypeError(e, m))
}

fn is_coercible(n: u128, ty: Type) -> bool {
    match ty {
        Type::Bool => n <= 1,
        Type::U8 => n <= u8::MAX as u128,
        Type::U16 => n <= u16::MAX as u128,
        Type::U32 => n <= u32::MAX as u128,
        Type::U64 => n <= u64::MAX as u128,
        Type::U128 => true,
    }
}

fn min_unsigned_type(n: u128) -> Type {
    if n <= u8::MAX as u128 {
        Type::U8
    } else if n <= u16::MAX as u128 {
        Type::U16
    } else if n <= u32::MAX as u128 {
        Type::U32
    } else if n <= u64::MAX as u128 {
        Type::U64
    } else {
        Type::U128
    }
}

impl Expr {
    fn type_check(&self, env: &mut Env<Type>) -> Result<typed_ast::Expr, TypeError> {
        let Expr(expr, meta) = self;
        let meta = *meta;
        let (expr, ty) = match expr {
            ExprEnum::True => (typed_ast::ExprEnum::True, Type::Bool),
            ExprEnum::False => (typed_ast::ExprEnum::False, Type::Bool),
            ExprEnum::NumUnsigned(n) => {
                (typed_ast::ExprEnum::NumUnsigned(*n), min_unsigned_type(*n))
            }
            ExprEnum::Identifier(s) => {
                if let Some(ty) = env.get(s) {
                    (typed_ast::ExprEnum::Identifier(s.clone()), ty)
                } else {
                    return Err(TypeError(TypeErrorEnum::IdentifierWithoutBinding(s.clone()), meta));
                }
            }
            ExprEnum::Op(op, x, y) => match op {
                Op::Add => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let ty = unify(&x, &y, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::BitAnd | Op::BitXor => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let ty = unify(&x, &y, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
            },
            ExprEnum::Let(var, binding, body) => {
                let binding = binding.type_check(env)?;
                env.push();
                env.set(var.clone(), binding.1);
                let body = body.type_check(env)?;
                env.pop();
                let ty = body.1;
                let expr = typed_ast::ExprEnum::Let(var.clone(), Box::new(binding), Box::new(body));
                (expr, ty)
            }
        };
        Ok(typed_ast::Expr(expr, ty, meta))
    }
}
