use std::collections::HashSet;

use crate::{
    ast::{Expr, ExprEnum, Op, ParamDef, Program, Type, UnaryOp},
    env::Env,
    parser::MetaInfo,
    typed_ast,
};

#[derive(Debug, Clone)]
pub struct TypeError(pub TypeErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum TypeErrorEnum {
    IdentifierWithoutBinding(String),
    MaxNumUnsignedSizeExceeded(Type, u128),
    ExpectedBoolOrNumberType(Type),
    ExpectedNumberType(Type),
    DuplicateFnParam(String),
    FnCannotBeUsedAsValue(String),
    ExpectedFnType {
        expected: Vec<Type>,
        actual: Type,
    },
    ExpectedFnArgTypes {
        expected: Vec<Type>,
        actual: Vec<Type>,
    },
    UnexpectedType {
        expected: Type,
        actual: Type,
    },
    TypeMismatch((Type, MetaInfo), (Type, MetaInfo)),
}

impl Program {
    pub fn type_check(&self) -> Result<typed_ast::Program, TypeError> {
        let mut env = Env::new();
        let mut fn_defs = Vec::with_capacity(self.fn_defs.len());
        for fn_def in self.fn_defs.iter() {
            let mut param_types = Vec::with_capacity(fn_def.params.len());

            env.push();
            let mut params = Vec::with_capacity(fn_def.params.len());
            let mut param_identifiers = HashSet::new();
            for param in fn_def.params.iter() {
                let ParamDef(identifier, ty) = param;
                if param_identifiers.contains(identifier) {
                    let e = TypeErrorEnum::DuplicateFnParam(identifier.clone());
                    return Err(TypeError(e, fn_def.meta));
                } else {
                    param_identifiers.insert(identifier);
                }
                env.set(identifier.clone(), ty.clone());
                params.push(param.clone());
                param_types.push(ty.clone());
            }
            let body = fn_def.body.type_check(&mut env)?;
            expect_type(&body, fn_def.ty.clone())?;
            env.pop();

            let fn_type = Type::Fn(param_types, Box::new(fn_def.ty.clone()));
            env.set(fn_def.identifier.clone(), fn_type);
            fn_defs.push(typed_ast::FnDef {
                identifier: fn_def.identifier.clone(),
                params,
                body,
                meta: fn_def.meta,
            })
        }
        let mut params = Vec::with_capacity(self.main.params.len());
        let mut param_identifiers = HashSet::new();
        for (party, param) in self.main.params.iter() {
            let ParamDef(identifier, ty) = param;
            if param_identifiers.contains(identifier) {
                let e = TypeErrorEnum::DuplicateFnParam(identifier.clone());
                return Err(TypeError(e, self.main.meta));
            } else {
                param_identifiers.insert(identifier);
            }
            env.set(identifier.clone(), ty.clone());
            params.push((*party, param.clone()));
        }
        let body = self.main.body.type_check(&mut env)?;
        expect_type(&body, self.main.ty.clone())?;
        let main = typed_ast::MainDef {
            params,
            body,
            meta: self.main.meta,
        };
        Ok(typed_ast::Program { fn_defs, main })
    }
}

fn expect_type(expr: &typed_ast::Expr, expected: Type) -> Result<(), TypeError> {
    let typed_ast::Expr(expr, actual, meta) = expr;
    let actual = actual.clone();
    if let typed_ast::ExprEnum::NumUnsigned(n) = expr {
        if is_coercible_unsigned(*n, &expected) {
            return Ok(());
        }
    }
    if let typed_ast::ExprEnum::NumSigned(n) = expr {
        if is_coercible_signed(*n, &expected) {
            return Ok(());
        }
    }
    if actual == expected {
        Ok(())
    } else {
        let e = TypeErrorEnum::UnexpectedType { expected, actual };
        Err(TypeError(e, *meta))
    }
}

fn expect_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeError> {
    match ty {
        Type::U8
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::U128
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::I128 => Ok(()),
        _ => {
            return Err(TypeError(
                TypeErrorEnum::ExpectedNumberType(ty.clone()),
                meta,
            ));
        }
    }
}

fn expect_signed_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeError> {
    match ty {
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => Ok(()),
        _ => {
            return Err(TypeError(
                TypeErrorEnum::ExpectedNumberType(ty.clone()),
                meta,
            ));
        }
    }
}

fn expect_bool_or_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeError> {
    if let Type::Bool = ty {
        Ok(())
    } else if let Ok(()) = expect_num_type(ty, meta) {
        Ok(())
    } else {
        Err(TypeError(
            TypeErrorEnum::ExpectedBoolOrNumberType(ty.clone()),
            meta,
        ))
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
        (typed_ast::ExprEnum::NumUnsigned(n1), typed_ast::ExprEnum::NumSigned(n2)) => {
            if *n2 >= 0 {
                let n2 = *n2 as u128;
                let n = if n1 > &n2 { n1 } else { &n2 };
                return Ok(min_unsigned_type(*n));
            } else if *n1 <= i128::MAX as u128 {
                let n1 = &(*n1 as i128);
                let n = if n1.abs() > n2.abs() { n1 } else { n2 };
                return Ok(min_signed_type(*n));
            }
        }
        (typed_ast::ExprEnum::NumSigned(n1), typed_ast::ExprEnum::NumUnsigned(n2)) => {
            if *n1 >= 0 {
                let n1 = *n1 as u128;
                let n = if n2 > &n1 { n2 } else { &n1 };
                return Ok(min_unsigned_type(*n));
            } else if *n2 <= i128::MAX as u128 {
                let n2 = &(*n2 as i128);
                let n = if n2.abs() > n1.abs() { n2 } else { n1 };
                return Ok(min_signed_type(*n));
            }
        }
        (typed_ast::ExprEnum::NumSigned(n1), typed_ast::ExprEnum::NumSigned(n2)) => {
            let n = if n1.abs() > n2.abs() { n1 } else { n2 };
            return Ok(min_signed_type(*n));
        }
        (typed_ast::ExprEnum::NumUnsigned(n), _) => {
            if is_coercible_unsigned(*n, ty2) {
                return Ok(ty2.clone());
            }
        }
        (_, typed_ast::ExprEnum::NumUnsigned(n)) => {
            if is_coercible_unsigned(*n, ty1) {
                return Ok(ty1.clone());
            }
        }
        (typed_ast::ExprEnum::NumSigned(n), _) => {
            if is_coercible_signed(*n, ty2) {
                return Ok(ty2.clone());
            }
        }
        (_, typed_ast::ExprEnum::NumSigned(n)) => {
            if is_coercible_signed(*n, ty1) {
                return Ok(ty1.clone());
            }
        }
        _ => {
            if *ty1 == *ty2 {
                return Ok(ty1.clone());
            }
        }
    }
    let e = TypeErrorEnum::TypeMismatch((ty1.clone(), *meta1), (ty2.clone(), *meta2));
    Err(TypeError(e, m))
}

fn is_coercible_unsigned(n: u128, ty: &Type) -> bool {
    match ty {
        Type::Bool => n <= 1,
        Type::U8 => n <= u8::MAX as u128,
        Type::U16 => n <= u16::MAX as u128,
        Type::U32 => n <= u32::MAX as u128,
        Type::U64 => n <= u64::MAX as u128,
        Type::U128 => true,
        Type::I8 => n <= i8::MAX as u128,
        Type::I16 => n <= i16::MAX as u128,
        Type::I32 => n <= i32::MAX as u128,
        Type::I64 => n <= i64::MAX as u128,
        Type::I128 => n <= i128::MAX as u128,
        Type::Fn(_, _) => false,
    }
}

fn is_coercible_signed(n: i128, ty: &Type) -> bool {
    match ty {
        Type::Bool => n <= 1,
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 => {
            if n < 0 {
                false
            } else {
                is_coercible_unsigned(n as u128, ty)
            }
        }
        Type::I8 => n >= i8::MIN as i128 && n <= i8::MAX as i128,
        Type::I16 => n >= i16::MIN as i128 && n <= i16::MAX as i128,
        Type::I32 => n >= i32::MIN as i128 && n <= i32::MAX as i128,
        Type::I64 => n >= i64::MIN as i128 && n <= i64::MAX as i128,
        Type::I128 => true,
        Type::Fn(_, _) => false,
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

fn min_signed_type(n: i128) -> Type {
    if n >= i8::MIN as i128 && n <= i8::MAX as i128 {
        Type::I8
    } else if n >= i16::MIN as i128 && n <= i16::MAX as i128 {
        Type::I16
    } else if n >= i32::MIN as i128 && n <= i32::MAX as i128 {
        Type::I32
    } else if n >= i64::MIN as i128 && n <= i64::MAX as i128 {
        Type::I64
    } else {
        Type::I128
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
            ExprEnum::NumSigned(n) => (typed_ast::ExprEnum::NumSigned(*n), min_signed_type(*n)),
            ExprEnum::Identifier(s) => {
                if let Some(ty) = env.get(s) {
                    (typed_ast::ExprEnum::Identifier(s.clone()), ty)
                } else {
                    return Err(TypeError(
                        TypeErrorEnum::IdentifierWithoutBinding(s.clone()),
                        meta,
                    ));
                }
            }
            ExprEnum::UnaryOp(UnaryOp::Neg, x) => {
                let x = x.type_check(env)?;
                let ty = x.1.clone();
                expect_signed_num_type(&ty, x.2)?;
                (typed_ast::ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(x)), ty)
            }
            ExprEnum::UnaryOp(UnaryOp::Not, x) => {
                let x = x.type_check(env)?;
                let ty = x.1.clone();
                expect_bool_or_num_type(&ty, x.2)?;
                (typed_ast::ExprEnum::UnaryOp(UnaryOp::Not, Box::new(x)), ty)
            }
            ExprEnum::Op(op, x, y) => match op {
                Op::Add | Op::Sub => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::BitAnd | Op::BitXor | Op::BitOr => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_bool_or_num_type(&ty, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::GreaterThan | Op::LessThan => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        Type::Bool,
                    )
                }
                Op::Eq | Op::NotEq => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_bool_or_num_type(&ty, meta)?;
                    let expr = typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y));
                    (expr, Type::Bool)
                }
                Op::ShiftLeft | Op::ShiftRight => {
                    let x = x.type_check(env)?;
                    let y = y.type_check(env)?;
                    let typed_ast::Expr(_, ty_x, meta_x) = x.clone();
                    expect_num_type(&ty_x, meta_x)?;
                    expect_type(&y, Type::U8)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        ty_x.clone(),
                    )
                }
            },
            ExprEnum::Let(var, binding, body) => {
                let binding = binding.type_check(env)?;
                if let Type::Fn(_, _) = binding.1 {
                    return Err(TypeError(
                        TypeErrorEnum::FnCannotBeUsedAsValue(var.clone()),
                        meta,
                    ));
                }
                env.push();
                env.set(var.clone(), binding.1.clone());
                let body = body.type_check(env)?;
                env.pop();
                let ty = body.1.clone();
                let expr = typed_ast::ExprEnum::Let(var.clone(), Box::new(binding), Box::new(body));
                (expr, ty)
            }
            ExprEnum::FnCall(identifier, args) => {
                if let Some(fn_type) = env.get(identifier) {
                    let mut arg_types = Vec::with_capacity(args.len());
                    let mut arg_meta = Vec::with_capacity(args.len());
                    let mut arg_exprs = Vec::with_capacity(args.len());
                    for arg in args.iter() {
                        let arg = arg.type_check(env)?;
                        let typed_ast::Expr(_, ty, meta) = &arg;
                        arg_types.push(ty.clone());
                        arg_meta.push(*meta);
                        arg_exprs.push(arg);
                    }
                    match fn_type {
                        Type::Fn(fn_arg_types, ret_ty) => {
                            if fn_arg_types.len() == arg_types.len() {
                                for (expected, actual) in fn_arg_types.into_iter().zip(&arg_exprs) {
                                    expect_type(actual, expected)?;
                                }
                                let expr =
                                    typed_ast::ExprEnum::FnCall(identifier.clone(), arg_exprs);
                                (expr, *ret_ty)
                            } else {
                                let e = TypeErrorEnum::ExpectedFnArgTypes {
                                    expected: arg_types,
                                    actual: fn_arg_types,
                                };
                                return Err(TypeError(e, meta));
                            }
                        }
                        actual => {
                            let e = TypeErrorEnum::ExpectedFnType {
                                expected: arg_types,
                                actual,
                            };
                            return Err(TypeError(e, meta));
                        }
                    }
                } else {
                    let e = TypeErrorEnum::IdentifierWithoutBinding(identifier.clone());
                    return Err(TypeError(e, meta));
                }
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.type_check(env)?;
                let case_true = case_true.type_check(env)?;
                let case_false = case_false.type_check(env)?;
                expect_type(&condition, Type::Bool)?;
                let ty = unify(&case_true, &case_false, meta)?;
                let expr = typed_ast::ExprEnum::If(
                    Box::new(condition),
                    Box::new(case_true),
                    Box::new(case_false),
                );
                (expr, ty)
            }
            ExprEnum::Cast(ty, expr) => {
                let expr = expr.type_check(env)?;
                let typed_ast::Expr(_, expr_ty, _) = &expr;
                expect_bool_or_num_type(expr_ty, meta)?;
                expect_bool_or_num_type(&ty, meta)?;
                (
                    typed_ast::ExprEnum::Cast(ty.clone(), Box::new(expr)),
                    ty.clone(),
                )
            }
        };
        Ok(typed_ast::Expr(expr, ty, meta))
    }
}
