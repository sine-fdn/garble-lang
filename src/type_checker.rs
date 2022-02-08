use std::collections::{HashMap, HashSet};

use crate::{
    ast::{
        Expr, ExprEnum, Op, ParamDef, Pattern, PatternEnum, Program, Type, UnaryOp, VariantExpr,
        VariantExprEnum,
    },
    env::Env,
    parser::MetaInfo,
    typed_ast,
};

#[derive(Debug, Clone)]
pub struct TypeError(pub TypeErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum TypeErrorEnum {
    UnknownEnum(String),
    UnknownEnumVariant(String, String),
    UnknownIdentifier(String),
    MaxNumUnsignedSizeExceeded(Type, u128),
    ExpectedBoolOrNumberType(Type),
    ExpectedNumberType(Type),
    ExpectedArrayType(Type),
    ExpectedTupleType(Type),
    TupleAccessOutOfBounds(usize),
    DuplicateFnParam(String),
    FnCannotBeUsedAsValue(String),
    ExpectedEnumType(Type),
    ExpectedEnumVariant(Vec<Type>),
    ExpectedUnitVariantFoundTupleVariant,
    ExpectedTupleVariantFoundUnitVariant,
    UnexpectedEnumVariantArity {
        expected: usize,
        actual: usize,
    },
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
    InvalidRange(usize, usize),
    PatternDoesNotMatchType(Type),
    PatternsAreNotExhaustive,
    TypeDoesNotSupportPatternMatching(Type),
}

struct Defs {
    enums: HashMap<String, HashMap<String, Option<Vec<Type>>>>,
}

impl Program {
    pub fn type_check(&self) -> Result<typed_ast::Program, TypeError> {
        let mut defs = Defs {
            enums: HashMap::new(),
        };
        for enum_def in self.enum_defs.iter() {
            let mut enum_variants = HashMap::new();
            for variant in &enum_def.variants {
                enum_variants.insert(variant.variant_name().to_string(), variant.types());
            }
            defs.enums
                .insert(enum_def.identifier.clone(), enum_variants);
        }
        let enum_defs = self.enum_defs.clone();

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
            let body = fn_def.body.type_check(&mut env, &defs)?;
            expect_type(&body, &fn_def.ty)?;
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
        let body = self.main.body.type_check(&mut env, &defs)?;
        expect_type(&body, &self.main.ty)?;
        let main = typed_ast::MainDef {
            params,
            body,
            meta: self.main.meta,
        };
        Ok(typed_ast::Program {
            enum_defs,
            fn_defs,
            main,
        })
    }
}

fn expect_type(expr: &typed_ast::Expr, expected: &Type) -> Result<(), TypeError> {
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
    if &actual == expected {
        Ok(())
    } else {
        let expected = expected.clone();
        let e = TypeErrorEnum::UnexpectedType { expected, actual };
        Err(TypeError(e, *meta))
    }
}

fn expect_array_type(ty: &Type, meta: MetaInfo) -> Result<(Type, usize), TypeError> {
    match ty {
        Type::Array(elem, size) => Ok((*elem.clone(), *size)),
        _ => Err(TypeError(
            TypeErrorEnum::ExpectedArrayType(ty.clone()),
            meta,
        )),
    }
}

fn expect_tuple_type(ty: &Type, meta: MetaInfo) -> Result<Vec<Type>, TypeError> {
    match ty {
        Type::Tuple(types) => Ok(types.clone()),
        _ => Err(TypeError(
            TypeErrorEnum::ExpectedTupleType(ty.clone()),
            meta,
        )),
    }
}

fn expect_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeError> {
    match ty {
        Type::Usize
        | Type::U8
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
        Type::Usize => n <= usize::MAX as u128,
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
        Type::Array(_, _) => false,
        Type::Tuple(_) => false,
        Type::Enum(_) => false,
    }
}

fn is_coercible_signed(n: i128, ty: &Type) -> bool {
    match ty {
        Type::Bool => n <= 1,
        Type::Usize | Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 => {
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
        Type::Array(_, _) => false,
        Type::Tuple(_) => false,
        Type::Enum(_) => false,
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
    fn type_check(&self, env: &mut Env<Type>, defs: &Defs) -> Result<typed_ast::Expr, TypeError> {
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
                    return Err(TypeError(TypeErrorEnum::UnknownIdentifier(s.clone()), meta));
                }
            }
            ExprEnum::ArrayLiteral(value, size) => {
                let value = value.type_check(env, defs)?;
                let ty = Type::Array(Box::new(value.1.clone()), *size);
                (
                    typed_ast::ExprEnum::ArrayLiteral(Box::new(value), *size),
                    ty,
                )
            }
            ExprEnum::ArrayAccess(arr, index) => {
                let arr = arr.type_check(env, defs)?;
                let index = index.type_check(env, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let (elem_ty, _) = expect_array_type(&array_ty, *array_meta)?;
                expect_type(&index, &Type::Usize)?;
                (
                    typed_ast::ExprEnum::ArrayAccess(Box::new(arr), Box::new(index)),
                    elem_ty,
                )
            }
            ExprEnum::ArrayAssignment(arr, index, value) => {
                let arr = arr.type_check(env, defs)?;
                let index = index.type_check(env, defs)?;
                let value = value.type_check(env, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let ty = array_ty.clone();
                let (elem_ty, _) = expect_array_type(&array_ty, *array_meta)?;
                expect_type(&index, &Type::Usize)?;
                expect_type(&value, &elem_ty)?;
                (
                    typed_ast::ExprEnum::ArrayAssignment(
                        Box::new(arr),
                        Box::new(index),
                        Box::new(value),
                    ),
                    ty,
                )
            }
            ExprEnum::TupleLiteral(values) => {
                let mut typed_values = Vec::with_capacity(values.len());
                let mut types = Vec::with_capacity(values.len());
                for v in values {
                    let typed = v.type_check(env, defs)?;
                    types.push(typed.1.clone());
                    typed_values.push(typed);
                }
                let ty = Type::Tuple(types);
                (typed_ast::ExprEnum::TupleLiteral(typed_values), ty)
            }
            ExprEnum::TupleAccess(tuple, index) => {
                let tuple = tuple.type_check(env, defs)?;
                let typed_ast::Expr(_, ty, meta) = &tuple;
                let value_types = expect_tuple_type(ty, *meta)?;
                if *index < value_types.len() {
                    let ty = value_types[*index].clone();
                    (
                        typed_ast::ExprEnum::TupleAccess(Box::new(tuple), *index),
                        ty,
                    )
                } else {
                    let e = TypeErrorEnum::TupleAccessOutOfBounds(*index);
                    return Err(TypeError(e, *meta));
                }
            }
            ExprEnum::UnaryOp(UnaryOp::Neg, x) => {
                let x = x.type_check(env, defs)?;
                let ty = x.1.clone();
                expect_signed_num_type(&ty, x.2)?;
                (typed_ast::ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(x)), ty)
            }
            ExprEnum::UnaryOp(UnaryOp::Not, x) => {
                let x = x.type_check(env, defs)?;
                let ty = x.1.clone();
                expect_bool_or_num_type(&ty, x.2)?;
                (typed_ast::ExprEnum::UnaryOp(UnaryOp::Not, Box::new(x)), ty)
            }
            ExprEnum::Op(op, x, y) => match op {
                Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Mod => {
                    let x = x.type_check(env, defs)?;
                    let y = y.type_check(env, defs)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::BitAnd | Op::BitXor | Op::BitOr => {
                    let x = x.type_check(env, defs)?;
                    let y = y.type_check(env, defs)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_bool_or_num_type(&ty, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::GreaterThan | Op::LessThan => {
                    let x = x.type_check(env, defs)?;
                    let y = y.type_check(env, defs)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        Type::Bool,
                    )
                }
                Op::Eq | Op::NotEq => {
                    let x = x.type_check(env, defs)?;
                    let y = y.type_check(env, defs)?;
                    let ty = unify(&x, &y, meta)?;
                    expect_bool_or_num_type(&ty, meta)?;
                    let expr = typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y));
                    (expr, Type::Bool)
                }
                Op::ShiftLeft | Op::ShiftRight => {
                    let x = x.type_check(env, defs)?;
                    let y = y.type_check(env, defs)?;
                    let typed_ast::Expr(_, ty_x, meta_x) = x.clone();
                    expect_num_type(&ty_x, meta_x)?;
                    expect_type(&y, &Type::U8)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        ty_x.clone(),
                    )
                }
            },
            ExprEnum::Let(var, binding, body) => {
                let binding = binding.type_check(env, defs)?;
                if let Type::Fn(_, _) = binding.1 {
                    return Err(TypeError(
                        TypeErrorEnum::FnCannotBeUsedAsValue(var.clone()),
                        meta,
                    ));
                }
                env.push();
                env.set(var.clone(), binding.1.clone());
                let body = body.type_check(env, defs)?;
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
                        let arg = arg.type_check(env, defs)?;
                        let typed_ast::Expr(_, ty, meta) = &arg;
                        arg_types.push(ty.clone());
                        arg_meta.push(*meta);
                        arg_exprs.push(arg);
                    }
                    match fn_type {
                        Type::Fn(fn_arg_types, ret_ty) => {
                            if fn_arg_types.len() == arg_types.len() {
                                for (expected, actual) in fn_arg_types.into_iter().zip(&arg_exprs) {
                                    expect_type(actual, &expected)?;
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
                    let e = TypeErrorEnum::UnknownIdentifier(identifier.clone());
                    return Err(TypeError(e, meta));
                }
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.type_check(env, defs)?;
                let case_true = case_true.type_check(env, defs)?;
                let case_false = case_false.type_check(env, defs)?;
                expect_type(&condition, &Type::Bool)?;
                let ty = unify(&case_true, &case_false, meta)?;
                let expr = typed_ast::ExprEnum::If(
                    Box::new(condition),
                    Box::new(case_true),
                    Box::new(case_false),
                );
                (expr, ty)
            }
            ExprEnum::Cast(ty, expr) => {
                let expr = expr.type_check(env, defs)?;
                let typed_ast::Expr(_, expr_ty, _) = &expr;
                expect_bool_or_num_type(expr_ty, meta)?;
                expect_bool_or_num_type(&ty, meta)?;
                (
                    typed_ast::ExprEnum::Cast(ty.clone(), Box::new(expr)),
                    ty.clone(),
                )
            }
            ExprEnum::Fold(arr, init, closure) => {
                let arr = arr.type_check(env, defs)?;
                let init = init.type_check(env, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let (elem_ty, _) = expect_array_type(&array_ty, *array_meta)?;
                if closure.params.len() != 2 {
                    let expected = vec![init.1, elem_ty];
                    let param_types = closure.params.iter().map(|p| p.1.clone()).collect();
                    let actual = Type::Fn(param_types, Box::new(closure.ty.clone()));
                    let e = TypeErrorEnum::ExpectedFnType { expected, actual };
                    return Err(TypeError(e, closure.meta));
                }
                let ParamDef(acc_identifier, acc_param_ty) = &closure.params[0];
                let ParamDef(elem_identifier, elem_param_ty) = &closure.params[1];
                expect_type(&init, &acc_param_ty)?;
                if &elem_ty != elem_param_ty {
                    let expected = elem_param_ty.clone();
                    let actual = elem_ty;
                    let e = TypeErrorEnum::UnexpectedType { expected, actual };
                    return Err(TypeError(e, closure.meta));
                }

                env.push();
                env.set(acc_identifier.clone(), acc_param_ty.clone());
                env.set(elem_identifier.clone(), elem_param_ty.clone());
                let body = closure.body.type_check(env, defs)?;
                unify(&init, &body, meta)?;
                env.pop();

                let ty = closure.ty.clone();
                expect_type(&body, &ty)?;

                let closure = typed_ast::Closure {
                    ty: closure.ty.clone(),
                    params: closure.params.clone(),
                    body,
                    meta,
                };
                (
                    typed_ast::ExprEnum::Fold(Box::new(arr), Box::new(init), Box::new(closure)),
                    ty,
                )
            }
            ExprEnum::Map(arr, closure) => {
                let arr = arr.type_check(env, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let (elem_ty, size) = expect_array_type(&array_ty, *array_meta)?;
                if closure.params.len() != 1 {
                    let expected = vec![elem_ty];
                    let param_types = closure.params.iter().map(|p| p.1.clone()).collect();
                    let actual = Type::Fn(param_types, Box::new(closure.ty.clone()));
                    let e = TypeErrorEnum::ExpectedFnType { expected, actual };
                    return Err(TypeError(e, closure.meta));
                }
                let ParamDef(elem_identifier, elem_param_ty) = &closure.params[0];
                if &elem_ty != elem_param_ty {
                    let expected = elem_param_ty.clone();
                    let actual = elem_ty;
                    let e = TypeErrorEnum::UnexpectedType { expected, actual };
                    return Err(TypeError(e, closure.meta));
                }

                env.push();
                env.set(elem_identifier.clone(), elem_param_ty.clone());
                let body = closure.body.type_check(env, defs)?;
                env.pop();

                expect_type(&body, &closure.ty)?;

                let ty = Type::Array(Box::new(closure.ty.clone()), size);

                let closure = typed_ast::Closure {
                    ty: closure.ty.clone(),
                    params: closure.params.clone(),
                    body,
                    meta,
                };
                (
                    typed_ast::ExprEnum::Map(Box::new(arr), Box::new(closure)),
                    ty,
                )
            }
            ExprEnum::Range(from, to) => {
                if from >= to {
                    let e = TypeErrorEnum::InvalidRange(*from, *to);
                    return Err(TypeError(e, meta));
                }
                let ty = Type::Array(Box::new(Type::Usize), to - from);
                (typed_ast::ExprEnum::Range(*from, *to), ty)
            }
            ExprEnum::EnumLiteral(identifier, variant) => {
                if let Some(enum_def) = defs.enums.get(identifier) {
                    let VariantExpr(variant_name, variant, meta) = variant.as_ref();
                    let meta = *meta;
                    if let Some(types) = enum_def.get(variant_name) {
                        match (variant, types) {
                            (VariantExprEnum::Unit, None) => {
                                let variant = typed_ast::VariantExpr(
                                    variant_name.to_string(),
                                    typed_ast::VariantExprEnum::Unit,
                                    meta,
                                );
                                let ty = Type::Enum(identifier.clone());
                                (
                                    typed_ast::ExprEnum::EnumLiteral(
                                        identifier.clone(),
                                        Box::new(variant),
                                    ),
                                    ty,
                                )
                            }
                            (VariantExprEnum::Tuple(values), Some(types)) => {
                                if values.len() != types.len() {
                                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                                        expected: types.len(),
                                        actual: values.len(),
                                    };
                                    return Err(TypeError(e, meta));
                                }
                                let mut exprs = Vec::with_capacity(values.len());
                                for (v, ty) in values.iter().zip(types) {
                                    let expr = v.type_check(env, defs)?;
                                    expect_type(&expr, ty)?;
                                    exprs.push(expr);
                                }
                                let variant = typed_ast::VariantExpr(
                                    variant_name.to_string(),
                                    typed_ast::VariantExprEnum::Tuple(exprs),
                                    meta,
                                );
                                let ty = Type::Enum(identifier.clone());
                                (
                                    typed_ast::ExprEnum::EnumLiteral(
                                        identifier.clone(),
                                        Box::new(variant),
                                    ),
                                    ty,
                                )
                            }
                            (VariantExprEnum::Unit, Some(types)) => {
                                let e = TypeErrorEnum::ExpectedEnumVariant(types.clone());
                                return Err(TypeError(e, meta));
                            }
                            (VariantExprEnum::Tuple(_), None) => {
                                let e = TypeErrorEnum::ExpectedEnumVariant(Vec::new());
                                return Err(TypeError(e, meta));
                            }
                        }
                    } else {
                        let e = TypeErrorEnum::UnknownEnumVariant(
                            identifier.clone(),
                            variant_name.to_string(),
                        );
                        return Err(TypeError(e, meta));
                    }
                } else {
                    let e = TypeErrorEnum::UnknownEnum(identifier.clone());
                    return Err(TypeError(e, meta));
                }
            }
            ExprEnum::Match(expr, clauses) => {
                let expr = expr.type_check(env, defs)?;
                let ty = &expr.1;

                match ty {
                    Type::Bool
                    | Type::Usize
                    | Type::U8
                    | Type::U16
                    | Type::U32
                    | Type::U64
                    | Type::U128
                    | Type::I8
                    | Type::I16
                    | Type::I32
                    | Type::I64
                    | Type::I128
                    | Type::Tuple(_)
                    | Type::Enum(_) => {}
                    Type::Fn(_, _) | Type::Array(_, _) => {
                        let e = TypeErrorEnum::TypeDoesNotSupportPatternMatching(ty.clone());
                        return Err(TypeError(e, meta));
                    }
                }

                let mut typed_clauses = Vec::with_capacity(clauses.len());

                for (pattern, expr) in clauses {
                    env.push();
                    let pattern = pattern.type_check(env, defs, ty.clone())?;
                    let expr = expr.type_check(env, defs)?;
                    env.pop();
                    typed_clauses.push((pattern, expr));
                }

                let ret_ty = {
                    let (_, typed_ast::Expr(_, ret_ty, _)) = &typed_clauses.get(0).unwrap();

                    for (_, expr) in typed_clauses.iter() {
                        let typed_ast::Expr(_, ty, meta) = expr;
                        if ret_ty != ty {
                            let e = TypeErrorEnum::UnexpectedType {
                                expected: ret_ty.clone(),
                                actual: ty.clone(),
                            };
                            return Err(TypeError(e, *meta));
                        }
                    }
                    ret_ty.clone()
                };

                check_exhaustiveness(&typed_clauses, &ty, &defs, meta)?;

                (
                    typed_ast::ExprEnum::Match(Box::new(expr), typed_clauses),
                    ret_ty,
                )
            }
        };
        Ok(typed_ast::Expr(expr, ty, meta))
    }
}

impl Pattern {
    fn type_check(
        &self,
        env: &mut Env<Type>,
        defs: &Defs,
        ty: Type,
    ) -> Result<typed_ast::Pattern, TypeError> {
        let Pattern(pattern, meta) = self;
        let meta = *meta;
        let pattern = match (pattern, &ty) {
            (PatternEnum::Identifier(s), _) => {
                env.set(s.clone(), ty.clone());
                typed_ast::PatternEnum::Identifier(s.clone())
            }
            (PatternEnum::True, Type::Bool) => typed_ast::PatternEnum::True,
            (PatternEnum::False, Type::Bool) => typed_ast::PatternEnum::False,
            (PatternEnum::NumUnsigned(n), ty) => {
                expect_num_type(&ty, meta)?;
                typed_ast::PatternEnum::NumUnsigned(*n)
            }
            (PatternEnum::NumSigned(n), ty) => {
                expect_signed_num_type(&ty, meta)?;
                typed_ast::PatternEnum::NumSigned(*n)
            }
            (PatternEnum::UnsignedInclusiveRange(from, to), ty) => {
                expect_num_type(&ty, meta)?;
                typed_ast::PatternEnum::UnsignedInclusiveRange(*from, *to)
            }
            (PatternEnum::SignedInclusiveRange(from, to), ty) => {
                expect_signed_num_type(&ty, meta)?;
                typed_ast::PatternEnum::SignedInclusiveRange(*from, *to)
            }
            (PatternEnum::Tuple(fields), ty) => {
                let field_types = expect_tuple_type(&ty, meta)?;
                if field_types.len() != fields.len() {
                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                        expected: field_types.len(),
                        actual: fields.len(),
                    };
                    return Err(TypeError(e, meta));
                }
                let mut typed_fields = Vec::with_capacity(fields.len());
                for (field, ty) in fields.iter().zip(field_types) {
                    typed_fields.push(field.type_check(env, defs, ty)?);
                }
                typed_ast::PatternEnum::Tuple(typed_fields)
            }
            (
                PatternEnum::EnumUnit(variant_name) | PatternEnum::EnumTuple(variant_name, _),
                Type::Enum(enum_name),
            ) => {
                if let Some(enum_def) = defs.enums.get(enum_name) {
                    if let Some(variant) = enum_def.get(variant_name) {
                        match (pattern, variant) {
                            (PatternEnum::EnumUnit(_), None) => {
                                typed_ast::PatternEnum::EnumUnit(variant_name.clone())
                            }
                            (PatternEnum::EnumTuple(_, fields), Some(field_types)) => {
                                if field_types.len() != fields.len() {
                                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                                        expected: field_types.len(),
                                        actual: fields.len(),
                                    };
                                    return Err(TypeError(e, meta));
                                }
                                let mut typed_fields = Vec::with_capacity(fields.len());
                                for (field, ty) in fields.iter().zip(field_types) {
                                    typed_fields.push(field.type_check(env, defs, ty.clone())?);
                                }
                                typed_ast::PatternEnum::EnumTuple(
                                    variant_name.clone(),
                                    typed_fields,
                                )
                            }
                            (PatternEnum::EnumUnit(_), Some(_)) => {
                                let e = TypeErrorEnum::ExpectedTupleVariantFoundUnitVariant;
                                return Err(TypeError(e, meta));
                            }
                            (PatternEnum::EnumTuple(_, _), None) => {
                                let e = TypeErrorEnum::ExpectedUnitVariantFoundTupleVariant;
                                return Err(TypeError(e, meta));
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        let e = TypeErrorEnum::UnknownEnumVariant(
                            enum_name.clone(),
                            variant_name.to_string(),
                        );
                        return Err(TypeError(e, meta));
                    }
                } else {
                    let e = TypeErrorEnum::UnknownEnum(enum_name.clone());
                    return Err(TypeError(e, meta));
                }
            }
            (_, _) => {
                let e = TypeErrorEnum::PatternDoesNotMatchType(ty);
                return Err(TypeError(e, meta));
            }
        };
        Ok(typed_ast::Pattern(pattern, ty, meta))
    }
}

fn check_exhaustiveness(
    clauses: &[(typed_ast::Pattern, typed_ast::Expr)],
    ty: &Type,
    defs: &Defs,
    meta: MetaInfo,
) -> Result<(), TypeError> {
    let patterns = clauses.iter().map(|(p, _)| vec![p.clone()]).collect();
    let wildcard_pattern = vec![typed_ast::Pattern(
        typed_ast::PatternEnum::Identifier("_".to_string()),
        ty.clone(),
        meta,
    )];
    if is_useful(patterns, wildcard_pattern, defs) {
        let e = TypeErrorEnum::PatternsAreNotExhaustive;
        return Err(TypeError(e, meta));
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum Ctor {
    True,
    False,
    UnsignedInclusiveRange(u128, u128),
    SignedInclusiveRange(i128, i128),
    Tuple(Vec<Type>),
    Variant(String, Option<Vec<Type>>),
}

type PatternStack = Vec<typed_ast::Pattern>;

fn specialize(ctor: &Ctor, pattern: &PatternStack) -> Vec<PatternStack> {
    let head = pattern.first().unwrap();
    let tail = pattern.iter().cloned().skip(1);
    let typed_ast::Pattern(head_enum, _, meta) = head;
    match ctor {
        Ctor::True => match head_enum {
            typed_ast::PatternEnum::Identifier(_) | typed_ast::PatternEnum::True => {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::False => match head_enum {
            typed_ast::PatternEnum::Identifier(_) | typed_ast::PatternEnum::False => {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::Variant(v1, fields) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                let field_types = fields.as_deref().unwrap_or_default();
                let mut fields = Vec::with_capacity(field_types.len());
                for ty in field_types {
                    let wildcard = typed_ast::PatternEnum::Identifier("_".to_string());
                    let p = typed_ast::Pattern(wildcard, ty.clone(), meta.clone());
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            typed_ast::PatternEnum::EnumUnit(v2) if v1 == v2 => vec![tail.collect()],
            typed_ast::PatternEnum::EnumTuple(v2, fields) if v1 == v2 => {
                vec![fields.into_iter().cloned().chain(tail).collect()]
            }
            _ => vec![],
        },
        Ctor::UnsignedInclusiveRange(min, max) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => vec![tail.collect()],
            typed_ast::PatternEnum::NumUnsigned(n) if n == min && n == max => vec![tail.collect()],
            typed_ast::PatternEnum::UnsignedInclusiveRange(n_min, n_max)
                if n_min <= min && max <= n_max =>
            {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::SignedInclusiveRange(min, max) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => vec![tail.collect()],
            typed_ast::PatternEnum::NumUnsigned(n)
                if *min >= 0 && *max >= 0 && *n == *min as u128 && *n == *max as u128 =>
            {
                vec![tail.collect()]
            }
            typed_ast::PatternEnum::NumSigned(n) if n == min && n == max => vec![tail.collect()],
            typed_ast::PatternEnum::UnsignedInclusiveRange(n_min, n_max)
                if *min >= 0 && *max >= 0 && *n_min <= *min as u128 && *max as u128 <= *n_max =>
            {
                vec![tail.collect()]
            }
            typed_ast::PatternEnum::SignedInclusiveRange(n_min, n_max)
                if n_min <= min && max <= n_max =>
            {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::Tuple(field_types) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                let mut fields = Vec::with_capacity(field_types.len());
                for ty in field_types {
                    let wildcard = typed_ast::PatternEnum::Identifier("_".to_string());
                    let p = typed_ast::Pattern(wildcard, ty.clone(), meta.clone());
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            typed_ast::PatternEnum::Tuple(fields) => {
                vec![fields.into_iter().cloned().chain(tail).collect()]
            }
            _ => vec![],
        },
    }
}

fn split_unsigned_range(patterns: &[PatternStack], min: u128, max: u128) -> Vec<Ctor> {
    let mut split_points = vec![min, max + 1];
    for p in patterns {
        let head = p.first().unwrap();
        let typed_ast::Pattern(head_enum, _, _) = head;
        match head_enum {
            typed_ast::PatternEnum::NumUnsigned(n) => split_points.push(*n),
            typed_ast::PatternEnum::NumSigned(n) if *n >= 0 => split_points.push(*n as u128),
            typed_ast::PatternEnum::UnsignedInclusiveRange(min, max) => {
                split_points.push(*min);
                split_points.push(*max + 1);
            }
            typed_ast::PatternEnum::SignedInclusiveRange(min, max) => {
                if *min >= 0 {
                    split_points.push(*min as u128);
                }
                if *max >= 0 {
                    split_points.push(*max as u128 + 1);
                }
            }
            _ => {}
        }
    }
    split_points.sort();
    split_points.dedup();
    let mut ranges = vec![];
    for range in split_points.windows(2) {
        if range[0] < range[1] - 1 {
            ranges.push(Ctor::UnsignedInclusiveRange(range[0], range[0]));
        }
        if range[0] >= min && range[1] - 1 <= max {
            ranges.push(Ctor::UnsignedInclusiveRange(range[0], range[1] - 1));
        }
    }
    ranges
}

fn split_signed_range(patterns: &[PatternStack], min: i128, max: i128) -> Vec<Ctor> {
    let mut split_points = vec![min, max + 1];
    for p in patterns {
        let head = p.first().unwrap();
        let typed_ast::Pattern(head_enum, _, _) = head;
        match head_enum {
            typed_ast::PatternEnum::NumUnsigned(n) => split_points.push(*n as i128),
            typed_ast::PatternEnum::NumSigned(n) if *n >= 0 => split_points.push(*n),
            typed_ast::PatternEnum::UnsignedInclusiveRange(min, max) => {
                split_points.push(*min as i128);
                split_points.push(*max as i128 + 1);
            }
            typed_ast::PatternEnum::SignedInclusiveRange(min, max) => {
                if *min >= 0 {
                    split_points.push(*min);
                }
                if *max >= 0 {
                    split_points.push(*max + 1);
                }
            }
            _ => {}
        }
    }
    split_points.sort();
    split_points.dedup();
    let mut ranges = vec![];
    for range in split_points.windows(2) {
        if range[0] < range[1] - 1 {
            ranges.push(Ctor::SignedInclusiveRange(range[0], range[0]));
        }
        if range[0] >= min && range[1] - 1 <= max {
            ranges.push(Ctor::SignedInclusiveRange(range[0], range[1] - 1));
        }
    }
    ranges
}

fn split_ctor(patterns: &[PatternStack], q: &PatternStack, defs: &Defs) -> Vec<Ctor> {
    let head = q.first().unwrap();
    let typed_ast::Pattern(head_enum, ty, _) = head;
    match ty {
        Type::Bool => vec![Ctor::True, Ctor::False],
        Type::Usize | Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 => {
            match head_enum {
                typed_ast::PatternEnum::Identifier(_) => {
                    split_unsigned_range(patterns, 0, u8::MAX as u128)
                }
                typed_ast::PatternEnum::NumUnsigned(n) => {
                    vec![Ctor::UnsignedInclusiveRange(*n, *n)]
                }
                typed_ast::PatternEnum::UnsignedInclusiveRange(min, max) => {
                    split_unsigned_range(patterns, *min, *max)
                }
                _ => panic!("cannot split {:?} for type {:?}", head_enum, ty),
            }
        }
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                vec![Ctor::SignedInclusiveRange(i8::MIN as i128, i8::MAX as i128)]
            }
            typed_ast::PatternEnum::NumUnsigned(n) => {
                vec![Ctor::SignedInclusiveRange(*n as i128, *n as i128)]
            }
            typed_ast::PatternEnum::NumSigned(n) => vec![Ctor::SignedInclusiveRange(*n, *n)],
            typed_ast::PatternEnum::UnsignedInclusiveRange(min, max) => {
                split_signed_range(patterns, *min as i128, *max as i128)
            }
            typed_ast::PatternEnum::SignedInclusiveRange(min, max) => {
                split_signed_range(patterns, *min, *max)
            }
            _ => panic!("cannot split {:?} for type {:?}", head_enum, ty),
        },
        Type::Enum(enum_name) => {
            let variants = defs.enums.get(enum_name).unwrap();
            variants
                .iter()
                .map(|(name, fields)| Ctor::Variant(name.clone(), fields.clone()))
                .collect()
        }
        Type::Tuple(fields) => {
            vec![Ctor::Tuple(fields.clone())]
        }
        Type::Fn(_, _) | Type::Array(_, _) => {
            panic!("Type {:?} does not support pattern matching", ty)
        }
    }
}

fn is_useful(patterns: Vec<PatternStack>, q: PatternStack, defs: &Defs) -> bool {
    if patterns.is_empty() {
        true
    } else if patterns[0].is_empty() || q.is_empty() {
        false
    } else {
        for ctor in split_ctor(&patterns, &q, defs) {
            let mut specialized = Vec::new();
            for p in patterns.iter() {
                let pattern_specialized = specialize(&ctor, &p);
                specialized.extend(pattern_specialized);
            }
            for q in specialize(&ctor, &q) {
                if is_useful(specialized.clone(), q.clone(), defs) {
                    return true;
                }
            }
        }
        false
    }
}
