//! Type-checker, transforming an untyped [`crate::ast::Program`] into a typed
//! [`crate::typed_ast::Program`].

use std::collections::{HashMap, HashSet};

use crate::{
    ast::{
        self, Expr, ExprEnum, FnDef, Op, ParamDef, Pattern, PatternEnum, Program, UnaryOp,
        VariantExpr, VariantExprEnum,
    },
    env::Env,
    token::{MetaInfo, SignedNumType, UnsignedNumType},
    typed_ast::{self, Type},
};

/// An error found during type-checking, with its location in the source code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeError(pub TypeErrorEnum, pub MetaInfo);

impl PartialOrd for TypeError {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.1.partial_cmp(&other.1)
    }
}

impl Ord for TypeError {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.1.cmp(&other.1)
    }
}

/// The different kinds of errors found during type-checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeErrorEnum {
    /// The identifier is not a top level function.
    NoTopLevelFn(String),
    /// The specified function does not have any input parameters.
    PubFnWithoutParams(String),
    /// A top-level function is declared but never used.
    UnusedFn(String),
    /// A top-level function calls itself recursively.
    RecursiveFnDef(String),
    /// No struct or enum declaration with the specified name exists.
    UnknownStructOrEnum(String),
    /// No struct declaration with the specified name exists.
    UnknownStruct(String),
    /// The struct exists, but does not contain a field with the specified name.
    UnknownStructField(String, String),
    /// The struct constructor is missing the specified field.
    MissingStructField(String, String),
    /// No enum declaration with the specified name exists.
    UnknownEnum(String),
    /// The enum exists, but no variant declaration with the specified name was found.
    UnknownEnumVariant(String, String),
    /// No variable or function with the specified name exists in the current scope.
    UnknownIdentifier(String),
    /// The index is larger than the specified tuple size.
    TupleAccessOutOfBounds(usize),
    /// A parameter name is used more than once in a function declaration.
    DuplicateFnParam(String),
    /// An boolean or number expression was expected.
    ExpectedBoolOrNumberType(Type),
    /// A number expression was expected.
    ExpectedNumberType(Type),
    /// A signed number expression was expected.
    ExpectedSignedNumberType(Type),
    /// An array type was expected.
    ExpectedArrayType(Type),
    /// A tuple type was expected.
    ExpectedTupleType(Type),
    /// A struct type was expected.
    ExpectedStructType(Type),
    /// An enum type was expected.
    ExpectedEnumType(Type),
    /// Expected an enum variant without fields, but found a tuple variant.
    ExpectedUnitVariantFoundTupleVariant,
    /// Expected an enum variant with fields, but found a unit variant.
    ExpectedTupleVariantFoundUnitVariant,
    /// Expected a different number of variant fields.
    UnexpectedEnumVariantArity {
        /// The expected number of fields.
        expected: usize,
        /// The actual number of fields.
        actual: usize,
    },
    /// Expected a different type.
    UnexpectedType {
        /// The expected type.
        expected: Type,
        /// The actual type.
        actual: Type,
    },
    /// Expected a different number of function arguments.
    WrongNumberOfArgs {
        /// The number of parameters declared by the function.
        expected: usize,
        /// The number of arguments provided by the caller.
        actual: usize,
    },
    /// The two types are incompatible, (e.g. incompatible number types in a `+` operation).
    TypeMismatch((Type, MetaInfo), (Type, MetaInfo)),
    /// The specified range has invalid min or max values.
    InvalidRange(usize, usize),
    /// The specified pattern does not match the type of the matched expression.
    PatternDoesNotMatchType(Type),
    /// The patterns do not cover all possible cases.
    PatternsAreNotExhaustive(Vec<PatternStack>),
    /// The expression cannot be matched upon.
    TypeDoesNotSupportPatternMatching(Type),
}

impl std::fmt::Display for TypeErrorEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeErrorEnum::NoTopLevelFn(fn_name) => f.write_fmt(format_args!("'{fn_name}' is not a top level function")),
            TypeErrorEnum::PubFnWithoutParams(fn_name) => f.write_fmt(format_args!("The function '{fn_name}' is declared pub, but has no parameters")),
            TypeErrorEnum::UnusedFn(name) => f.write_fmt(format_args!(
                "Function '{name}' is declared but never used"
            )),
            TypeErrorEnum::RecursiveFnDef(name) => f.write_fmt(format_args!(
                "Function '{name}' is declared recursively, which is not supported"
            )),
            TypeErrorEnum::UnknownStructOrEnum(name) => {
                f.write_fmt(format_args!("Unknown struct or enum '{name}'"))
            }
            TypeErrorEnum::UnknownStruct(struct_name) => {
                f.write_fmt(format_args!("Unknown struct '{struct_name}'"))
            }
            TypeErrorEnum::UnknownStructField(struct_name, struct_field) => f.write_fmt(
                format_args!("Struct '{struct_name}' does not have a field '{struct_field}'"),
            ),
            TypeErrorEnum::MissingStructField(struct_name, struct_field) => f.write_fmt(
                format_args!("Field '{struct_field}' is missing for struct '{struct_name}'"),
            ),
            TypeErrorEnum::UnknownEnum(enum_name) => {
                f.write_fmt(format_args!("Unknown enum '{enum_name}'"))
            }
            TypeErrorEnum::UnknownEnumVariant(enum_name, enum_variant) => f.write_fmt(
                format_args!("Unknown enum variant '{enum_name}::{enum_variant}'"),
            ),
            TypeErrorEnum::UnknownIdentifier(name) => {
                f.write_fmt(format_args!("Unknown identifier '{name}'"))
            }
            TypeErrorEnum::TupleAccessOutOfBounds(size) => {
                f.write_fmt(format_args!("The tuple only has {size} fields"))
            }
            TypeErrorEnum::DuplicateFnParam(name) => f.write_fmt(format_args!(
                "The function parameter '{name}' is declared multiple times"
            )),
            TypeErrorEnum::ExpectedBoolOrNumberType(ty) => f.write_fmt(format_args!(
                "Expected a boolean or number type, but found {ty}"
            )),
            TypeErrorEnum::ExpectedNumberType(ty) => {
                f.write_fmt(format_args!("Expected a number type, but found {ty}"))
            }
            TypeErrorEnum::ExpectedSignedNumberType(ty) => f.write_fmt(format_args!(
                "Expected a signed number type, but found {ty}"
            )),
            TypeErrorEnum::ExpectedArrayType(ty) => {
                f.write_fmt(format_args!("Expected an array type, but found {ty}"))
            }
            TypeErrorEnum::ExpectedTupleType(ty) => {
                f.write_fmt(format_args!("Expected a tuple type, but found {ty}"))
            }
            TypeErrorEnum::ExpectedStructType(ty) => {
                f.write_fmt(format_args!("Expected a struct type, but found {ty}"))
            }
            TypeErrorEnum::ExpectedEnumType(ty) => {
                f.write_fmt(format_args!("Expected an enum type, but found {ty}"))
            }
            TypeErrorEnum::ExpectedUnitVariantFoundTupleVariant => {
                f.write_str("Expected a variant without fields, but found a tuple variant")
            }
            TypeErrorEnum::ExpectedTupleVariantFoundUnitVariant => {
                f.write_str("Expected a tuple variant, but found a variant without fields")
            }
            TypeErrorEnum::UnexpectedEnumVariantArity { expected, actual } => {
                f.write_fmt(format_args!(
                    "Expected a variant with {expected} fields, but found {actual} fields"
                ))
            }
            TypeErrorEnum::UnexpectedType { expected, actual } => {
                f.write_fmt(format_args!("Expected type {expected}, but found {actual}"))
            }
            TypeErrorEnum::WrongNumberOfArgs { expected, actual } => {
                f.write_fmt(format_args!("The function expects {expected} parameter(s), but was called with {actual} argument(s)"))
            }
            TypeErrorEnum::TypeMismatch((x, _), (y, _)) => f.write_fmt(format_args!(
                "The operands have incompatible types; {x} vs {y}"
            )),
            TypeErrorEnum::InvalidRange(_, _) => f.write_str("Invalid range"),
            TypeErrorEnum::PatternDoesNotMatchType(ty) => {
                f.write_fmt(format_args!("The pattern does not match the type {ty}"))
            }
            TypeErrorEnum::PatternsAreNotExhaustive(missing) => {
                f.write_str("The patterns are not exhaustive. Missing cases:\n\n")?;
                for pattern in missing {
                    f.write_str("  ")?;
                    let mut fields = pattern.iter();
                    if let Some(field) = fields.next() {
                        field.fmt(f)?;
                    }
                    for field in fields {
                        f.write_str(", ")?;
                        field.fmt(f)?;
                    }
                    f.write_str("\n\n")?;
                }
                f.write_str("...in expression")
            }
            TypeErrorEnum::TypeDoesNotSupportPatternMatching(ty) => {
                f.write_fmt(format_args!("Type {ty} does not support pattern matching"))
            }
        }
    }
}

pub(crate) struct TopLevelTypes<'a> {
    pub(crate) struct_names: HashSet<&'a String>,
    pub(crate) enum_names: HashSet<&'a String>,
}

impl ast::PreliminaryType {
    fn as_concrete_type(&self, types: &TopLevelTypes) -> Result<Type, TypeError> {
        let ty = match self {
            ast::PreliminaryType::Bool => Type::Bool,
            ast::PreliminaryType::Unsigned(n) => Type::Unsigned(*n),
            ast::PreliminaryType::Signed(n) => Type::Signed(*n),
            ast::PreliminaryType::Fn(args, ret) => {
                let mut concrete_args = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    concrete_args.push(arg.as_concrete_type(types)?);
                }
                let ret = ret.as_concrete_type(types)?;
                Type::Fn(concrete_args, Box::new(ret))
            }
            ast::PreliminaryType::Array(elem, size) => {
                let elem = elem.as_concrete_type(types)?;
                Type::Array(Box::new(elem), *size)
            }
            ast::PreliminaryType::Tuple(fields) => {
                let mut concrete_fields = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    concrete_fields.push(field.as_concrete_type(types)?);
                }
                Type::Tuple(concrete_fields)
            }
            ast::PreliminaryType::StructOrEnum(name, meta) => {
                if types.struct_names.contains(name) {
                    Type::Struct(name.clone())
                } else if types.enum_names.contains(name) {
                    Type::Enum(name.clone())
                } else {
                    let e = TypeErrorEnum::UnknownStructOrEnum(name.clone());
                    return Err(TypeError(e, *meta));
                }
            }
        };
        Ok(ty)
    }
}

/// Static top-level definitions of enums and functions.
pub struct Defs<'a> {
    structs: HashMap<&'a str, (Vec<&'a str>, HashMap<&'a str, Type>)>,
    enums: HashMap<&'a str, HashMap<&'a str, Option<Vec<Type>>>>,
    fns: HashMap<&'a str, &'a FnDef>,
}

impl<'a> Defs<'a> {
    pub(crate) fn new(
        struct_defs: &'a HashMap<String, typed_ast::StructDef>,
        enum_defs: &'a HashMap<String, typed_ast::EnumDef>,
    ) -> Self {
        let mut defs = Self {
            structs: HashMap::new(),
            enums: HashMap::new(),
            fns: HashMap::new(),
        };
        for (struct_name, struct_def) in struct_defs.iter() {
            let mut field_names = Vec::with_capacity(struct_def.fields.len());
            let mut field_types = HashMap::with_capacity(struct_def.fields.len());
            for (field_name, field_type) in &struct_def.fields {
                field_names.push(field_name.as_str());
                field_types.insert(field_name.as_str(), field_type.clone());
            }
            defs.structs.insert(struct_name, (field_names, field_types));
        }
        for (enum_name, enum_def) in enum_defs.iter() {
            let mut enum_variants = HashMap::new();
            for variant in &enum_def.variants {
                enum_variants.insert(variant.variant_name(), variant.types());
            }
            defs.enums.insert(enum_name, enum_variants);
        }
        defs
    }
}

pub(crate) struct TypedFns {
    currently_being_checked: HashSet<String>,
    typed: HashMap<String, Result<typed_ast::FnDef, Vec<TypeError>>>,
}

impl TypedFns {
    pub(crate) fn new() -> Self {
        Self {
            currently_being_checked: HashSet::new(),
            typed: HashMap::new(),
        }
    }
}

impl Program {
    /// Type-checks the parsed program, returning either a typed AST or type errors.
    pub fn type_check(&self) -> Result<typed_ast::Program, Vec<TypeError>> {
        let mut errors = vec![];
        let mut struct_names = HashSet::with_capacity(self.struct_defs.len());
        let mut enum_names = HashSet::with_capacity(self.enum_defs.len());
        struct_names.extend(self.struct_defs.keys());
        enum_names.extend(self.enum_defs.keys());
        let top_level_defs = TopLevelTypes {
            struct_names,
            enum_names,
        };
        let mut struct_defs = HashMap::with_capacity(self.struct_defs.len());
        for (struct_name, struct_def) in self.struct_defs.iter() {
            let meta = struct_def.meta;
            let mut fields = Vec::with_capacity(struct_def.fields.len());
            for (name, ty) in struct_def.fields.iter() {
                match ty.as_concrete_type(&top_level_defs) {
                    Ok(ty) => fields.push((name.clone(), ty)),
                    Err(e) => errors.push(e),
                }
            }
            struct_defs.insert(struct_name.clone(), typed_ast::StructDef { fields, meta });
        }
        let mut enum_defs = HashMap::with_capacity(self.enum_defs.len());
        for (enum_name, enum_def) in self.enum_defs.iter() {
            let meta = enum_def.meta;
            let mut variants = Vec::with_capacity(enum_def.variants.len());
            for variant in enum_def.variants.iter() {
                variants.push(match variant {
                    ast::Variant::Unit(variant_name) => {
                        typed_ast::Variant::Unit(variant_name.clone())
                    }
                    ast::Variant::Tuple(variant_name, variant_fields) => {
                        let mut fields = Vec::with_capacity(variant_fields.len());
                        for field in variant_fields.iter() {
                            match field.as_concrete_type(&top_level_defs) {
                                Ok(field) => fields.push(field),
                                Err(e) => errors.push(e),
                            }
                        }
                        typed_ast::Variant::Tuple(variant_name.clone(), fields)
                    }
                });
            }
            enum_defs.insert(enum_name.clone(), typed_ast::EnumDef { variants, meta });
        }

        let mut defs = Defs::new(&struct_defs, &enum_defs);

        let mut checked_fn_defs = TypedFns::new();
        for (fn_name, fn_def) in self.fn_defs.iter() {
            defs.fns.insert(fn_name, fn_def);
        }
        for (fn_name, fn_def) in self.fn_defs.iter() {
            if fn_def.is_pub {
                if fn_def.params.is_empty() {
                    let e = TypeErrorEnum::PubFnWithoutParams(fn_name.clone());
                    errors.push(TypeError(e, fn_def.meta));
                } else {
                    let typed_fn = fn_def.type_check(&top_level_defs, &mut checked_fn_defs, &defs);
                    if let Err(e) = typed_fn.clone() {
                        errors.extend(e);
                    }
                    checked_fn_defs.typed.insert(fn_name.clone(), typed_fn);
                }
            }
        }
        for (fn_name, fn_def) in self.fn_defs.iter() {
            if !fn_def.is_pub && !checked_fn_defs.typed.contains_key(fn_name.as_str()) {
                let e = TypeErrorEnum::UnusedFn(fn_name.to_string());
                errors.push(TypeError(e, fn_def.meta));
            }
        }
        let mut fn_defs = HashMap::new();
        for (fn_name, fn_def) in checked_fn_defs.typed.into_iter() {
            if let Ok(fn_def) = fn_def {
                fn_defs.insert(fn_name, fn_def);
            }
        }
        if errors.is_empty() {
            Ok(typed_ast::Program {
                struct_defs,
                enum_defs,
                fn_defs,
            })
        } else {
            errors.sort();
            Err(errors)
        }
    }
}

impl FnDef {
    fn type_check(
        &self,
        top_level_defs: &TopLevelTypes,
        fns: &mut TypedFns,
        defs: &Defs,
    ) -> Result<typed_ast::FnDef, Vec<TypeError>> {
        if fns.currently_being_checked.contains(&self.identifier) {
            let e = TypeErrorEnum::RecursiveFnDef(self.identifier.clone());
            return Err(vec![TypeError(e, self.meta)]);
        } else {
            fns.currently_being_checked.insert(self.identifier.clone());
        }
        let mut errors = vec![];
        let mut env = Env::new();
        env.push();
        let mut params = Vec::with_capacity(self.params.len());
        let mut param_identifiers = HashSet::new();
        for param in self.params.iter() {
            let ParamDef(identifier, ty) = param;
            if param_identifiers.contains(identifier) {
                let e = TypeErrorEnum::DuplicateFnParam(identifier.clone());
                errors.push(TypeError(e, self.meta));
            } else {
                param_identifiers.insert(identifier);
            }
            match ty.as_concrete_type(top_level_defs) {
                Ok(ty) => {
                    env.set(identifier.clone(), ty.clone());
                    params.push(typed_ast::ParamDef(identifier.clone(), ty));
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }
        let mut body = self.body.type_check(top_level_defs, &mut env, fns, defs)?;
        match self.ty.as_concrete_type(top_level_defs) {
            Ok(ret_ty) => {
                if let Err(e) = coerce_type(&mut body, &ret_ty) {
                    errors.extend(e);
                }
            }
            Err(e) => errors.push(e),
        }
        env.pop();

        fns.currently_being_checked.remove(&self.identifier);

        if errors.is_empty() {
            Ok(typed_ast::FnDef {
                is_pub: self.is_pub,
                identifier: self.identifier.clone(),
                params,
                body,
                meta: self.meta,
            })
        } else {
            Err(errors)
        }
    }
}

impl Expr {
    pub(crate) fn type_check(
        &self,
        top_level_defs: &TopLevelTypes,
        env: &mut Env<Type>,
        fns: &mut TypedFns,
        defs: &Defs,
    ) -> Result<typed_ast::Expr, Vec<TypeError>> {
        let Expr(expr, meta) = self;
        let meta = *meta;
        let (expr, ty) = match expr {
            ExprEnum::True => (typed_ast::ExprEnum::True, Type::Bool),
            ExprEnum::False => (typed_ast::ExprEnum::False, Type::Bool),
            ExprEnum::NumUnsigned(n, type_suffix) => {
                if let Some(type_suffix) = *type_suffix {
                    (
                        typed_ast::ExprEnum::NumUnsigned(*n, Some(type_suffix)),
                        Type::Unsigned(type_suffix),
                    )
                } else {
                    (
                        typed_ast::ExprEnum::NumSigned(*n as i128, None),
                        Type::Signed(SignedNumType::I32),
                    )
                }
            }
            ExprEnum::NumSigned(n, type_suffix) => (
                typed_ast::ExprEnum::NumSigned(*n, *type_suffix),
                Type::Signed(type_suffix.unwrap_or(SignedNumType::I32)),
            ),
            ExprEnum::Identifier(s) => {
                if let Some(ty) = env.get(s) {
                    (typed_ast::ExprEnum::Identifier(s.clone()), ty)
                } else {
                    return Err(vec![TypeError(
                        TypeErrorEnum::UnknownIdentifier(s.clone()),
                        meta,
                    )]);
                }
            }
            ExprEnum::ArrayLiteral(fields) => {
                let mut errors = vec![];
                let array_size = fields.len();
                let mut fields = fields.iter();
                let first_field =
                    fields
                        .next()
                        .unwrap()
                        .type_check(top_level_defs, env, fns, defs)?;
                let first_ty = first_field.1.clone();
                let first_meta = first_field.2;
                let mut typed_fields = vec![first_field];
                for field in fields {
                    match field.type_check(top_level_defs, env, fns, defs) {
                        Ok(field) => {
                            if field.1 != first_ty {
                                let e = TypeErrorEnum::TypeMismatch(
                                    (first_ty.clone(), first_meta),
                                    (field.1.clone(), field.2),
                                );
                                errors.push(TypeError(e, field.2));
                            }
                            typed_fields.push(field);
                        }
                        Err(e) => errors.extend(e),
                    }
                }
                if errors.is_empty() {
                    let ty = Type::Array(Box::new(first_ty), array_size);
                    (typed_ast::ExprEnum::ArrayLiteral(typed_fields), ty)
                } else {
                    return Err(errors);
                }
            }
            ExprEnum::ArrayRepeatLiteral(value, size) => {
                let value = value.type_check(top_level_defs, env, fns, defs)?;
                let ty = Type::Array(Box::new(value.1.clone()), *size);
                (
                    typed_ast::ExprEnum::ArrayRepeatLiteral(Box::new(value), *size),
                    ty,
                )
            }
            ExprEnum::ArrayAccess(arr, index) => {
                let arr = arr.type_check(top_level_defs, env, fns, defs)?;
                let mut index = index.type_check(top_level_defs, env, fns, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let (elem_ty, _) = expect_array_type(array_ty, *array_meta)?;
                coerce_type(&mut index, &Type::Unsigned(UnsignedNumType::Usize))?;
                (
                    typed_ast::ExprEnum::ArrayAccess(Box::new(arr), Box::new(index)),
                    elem_ty,
                )
            }
            ExprEnum::ArrayAssignment(arr, index, value) => {
                let arr = arr.type_check(top_level_defs, env, fns, defs)?;
                let mut index = index.type_check(top_level_defs, env, fns, defs)?;
                let mut value = value.type_check(top_level_defs, env, fns, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let ty = array_ty.clone();
                let (elem_ty, _) = expect_array_type(array_ty, *array_meta)?;
                coerce_type(&mut index, &Type::Unsigned(UnsignedNumType::Usize))?;
                coerce_type(&mut value, &elem_ty)?;
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
                let mut errors = vec![];
                let mut typed_values = Vec::with_capacity(values.len());
                let mut types = Vec::with_capacity(values.len());
                for v in values {
                    match v.type_check(top_level_defs, env, fns, defs) {
                        Ok(typed) => {
                            types.push(typed.1.clone());
                            typed_values.push(typed);
                        }
                        Err(e) => {
                            errors.extend(e);
                        }
                    }
                }
                if errors.is_empty() {
                    let ty = Type::Tuple(types);
                    (typed_ast::ExprEnum::TupleLiteral(typed_values), ty)
                } else {
                    return Err(errors);
                }
            }
            ExprEnum::TupleAccess(tuple, index) => {
                let tuple = tuple.type_check(top_level_defs, env, fns, defs)?;
                let typed_ast::Expr(_, ty, meta) = &tuple;
                let value_types = expect_tuple_type(ty, *meta)?;
                if *index < value_types.len() {
                    let ty = value_types[*index].clone();
                    (
                        typed_ast::ExprEnum::TupleAccess(Box::new(tuple), *index),
                        ty,
                    )
                } else {
                    let e = TypeErrorEnum::TupleAccessOutOfBounds(value_types.len());
                    return Err(vec![TypeError(e, *meta)]);
                }
            }
            ExprEnum::UnaryOp(UnaryOp::Neg, x) => {
                let x = x.type_check(top_level_defs, env, fns, defs)?;
                let ty = x.1.clone();
                expect_signed_num_type(&ty, x.2)?;
                (typed_ast::ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(x)), ty)
            }
            ExprEnum::UnaryOp(UnaryOp::Not, x) => {
                let x = x.type_check(top_level_defs, env, fns, defs)?;
                let ty = x.1.clone();
                expect_bool_or_num_type(&ty, x.2)?;
                (typed_ast::ExprEnum::UnaryOp(UnaryOp::Not, Box::new(x)), ty)
            }
            ExprEnum::Op(op, x, y) => match op {
                Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Mod => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let ty = unify(&mut x, &mut y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::ShortCircuitAnd | Op::ShortCircuitOr => {
                    let x = x.type_check(top_level_defs, env, fns, defs)?;
                    let y = y.type_check(top_level_defs, env, fns, defs)?;
                    for (ty, meta) in [(&x.1, &x.2), (&y.1, &y.2)] {
                        match ty {
                            Type::Bool => {}
                            ty => {
                                return Err(vec![TypeError(
                                    TypeErrorEnum::UnexpectedType {
                                        expected: Type::Bool,
                                        actual: ty.clone(),
                                    },
                                    *meta,
                                )])
                            }
                        }
                    }
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        Type::Bool,
                    )
                }
                Op::BitAnd | Op::BitXor | Op::BitOr => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let ty = unify(&mut x, &mut y, meta)?;
                    expect_bool_or_num_type(&ty, meta)?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::GreaterThan | Op::LessThan => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let ty = unify(&mut x, &mut y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (
                        typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)),
                        Type::Bool,
                    )
                }
                Op::Eq | Op::NotEq => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    unify(&mut x, &mut y, meta)?;
                    let expr = typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y));
                    (expr, Type::Bool)
                }
                Op::ShiftLeft | Op::ShiftRight => {
                    let x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let typed_ast::Expr(_, ty_x, meta_x) = x.clone();
                    expect_num_type(&ty_x, meta_x)?;
                    coerce_type(&mut y, &Type::Unsigned(UnsignedNumType::U8))?;
                    (typed_ast::ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty_x)
                }
            },
            ExprEnum::LexicallyScopedBlock(expr) => {
                env.push();
                let typed_ast::Expr(expr, ty, _) =
                    expr.type_check(top_level_defs, env, fns, defs)?;
                env.pop();
                (expr, ty)
            }
            ExprEnum::Let(bindings, body) => {
                let mut errors = vec![];
                let mut typed_bindings = Vec::with_capacity(bindings.len());
                for (var, binding) in bindings {
                    env.push();
                    match binding.type_check(top_level_defs, env, fns, defs) {
                        Ok(binding) => {
                            env.set(var.clone(), binding.1.clone());
                            typed_bindings.push((var.clone(), binding));
                        }
                        Err(e) => {
                            errors.extend(e);
                        }
                    }
                }
                match body.type_check(top_level_defs, env, fns, defs) {
                    Ok(body) => {
                        if errors.is_empty() {
                            for _ in bindings {
                                env.pop();
                            }
                            let ty = body.1.clone();
                            let expr = typed_ast::ExprEnum::Let(typed_bindings, Box::new(body));
                            (expr, ty)
                        } else {
                            return Err(errors);
                        }
                    }
                    Err(e) => {
                        errors.extend(e);
                        return Err(errors);
                    }
                }
            }
            ExprEnum::FnCall(identifier, args) => {
                if !fns.typed.contains_key(identifier) {
                    if let Some(fn_def) = defs.fns.get(identifier.as_str()) {
                        let fn_def = fn_def.type_check(top_level_defs, fns, defs);
                        fns.typed.insert(identifier.clone(), fn_def.clone());
                        if let Err(e) = fn_def {
                            return Err(e);
                        }
                    }
                }
                match (fns.typed.get(identifier), env.get(identifier)) {
                    (Some(Ok(fn_def)), None) => {
                        let typed_ast::Expr(_, ret_ty, _) = &fn_def.body;
                        let mut fn_arg_types = Vec::with_capacity(fn_def.params.len());
                        for typed_ast::ParamDef(_, ty) in fn_def.params.iter() {
                            fn_arg_types.push(ty.clone());
                        }
                        let ret_ty = ret_ty.clone();

                        let mut errors = vec![];
                        let mut arg_types = Vec::with_capacity(args.len());
                        let mut arg_meta = Vec::with_capacity(args.len());
                        let mut arg_exprs = Vec::with_capacity(args.len());
                        for arg in args.iter() {
                            match arg.type_check(top_level_defs, env, fns, defs) {
                                Ok(arg) => {
                                    let typed_ast::Expr(_, ty, meta) = &arg;
                                    arg_types.push(ty.clone());
                                    arg_meta.push(*meta);
                                    arg_exprs.push(arg);
                                }
                                Err(e) => errors.extend(e),
                            }
                        }
                        if fn_arg_types.len() != arg_types.len() {
                            let e = TypeErrorEnum::WrongNumberOfArgs {
                                expected: fn_arg_types.len(),
                                actual: arg_types.len(),
                            };
                            errors.push(TypeError(e, meta));
                        }
                        for (expected, actual) in fn_arg_types.into_iter().zip(&mut arg_exprs) {
                            if let Err(e) = coerce_type(actual, &expected) {
                                errors.extend(e);
                            }
                        }
                        if errors.is_empty() {
                            let expr = typed_ast::ExprEnum::FnCall(identifier.clone(), arg_exprs);
                            (expr, ret_ty)
                        } else {
                            return Err(errors);
                        }
                    }
                    (Some(Err(_)), None) => {
                        // error was added during typechecking of fn, no need to add error here
                        return Err(vec![]);
                    }
                    (None, _) => {
                        let e = TypeErrorEnum::UnknownIdentifier(identifier.clone());
                        return Err(vec![TypeError(e, meta)]);
                    }
                    (_, Some(_)) => {
                        let e = TypeErrorEnum::NoTopLevelFn(identifier.clone());
                        return Err(vec![TypeError(e, meta)]);
                    }
                }
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.type_check(top_level_defs, env, fns, defs);
                let case_true = case_true.type_check(top_level_defs, env, fns, defs);
                let case_false = case_false.type_check(top_level_defs, env, fns, defs);
                match (condition, case_true, case_false) {
                    (Ok(mut condition), Ok(mut case_true), Ok(mut case_false)) => {
                        coerce_type(&mut condition, &Type::Bool)?;
                        let ty = unify(&mut case_true, &mut case_false, meta)?;
                        let expr = typed_ast::ExprEnum::If(
                            Box::new(condition),
                            Box::new(case_true),
                            Box::new(case_false),
                        );
                        (expr, ty)
                    }
                    (condition, case_true, case_false) => {
                        let mut errors = vec![];
                        if let Err(e) = condition {
                            errors.extend(e);
                        }
                        if let Err(e) = case_true {
                            errors.extend(e);
                        }
                        if let Err(e) = case_false {
                            errors.extend(e);
                        }
                        return Err(errors);
                    }
                }
            }
            ExprEnum::Cast(ty, expr) => {
                let ty = ty.as_concrete_type(top_level_defs).map_err(|e| vec![e])?;
                let expr = expr.type_check(top_level_defs, env, fns, defs)?;
                let typed_ast::Expr(_, expr_ty, _) = &expr;
                expect_bool_or_num_type(expr_ty, meta)?;
                expect_bool_or_num_type(&ty, meta)?;
                (typed_ast::ExprEnum::Cast(ty.clone(), Box::new(expr)), ty)
            }
            ExprEnum::Fold(arr, init, closure) => {
                let arr = arr.type_check(top_level_defs, env, fns, defs)?;
                let mut init = init.type_check(top_level_defs, env, fns, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let (elem_ty, _) = expect_array_type(array_ty, *array_meta)?;
                let closure_ty = closure
                    .ty
                    .as_concrete_type(top_level_defs)
                    .map_err(|e| vec![e])?;
                let mut params = Vec::with_capacity(closure.params.len());
                let mut param_types = Vec::with_capacity(closure.params.len());
                for ParamDef(name, ty) in closure.params.iter() {
                    let ty = ty.as_concrete_type(top_level_defs).map_err(|e| vec![e])?;
                    params.push(typed_ast::ParamDef(name.clone(), ty.clone()));
                    param_types.push(ty);
                }
                if closure.params.len() != 2 {
                    let expected = Type::Fn(vec![init.1, elem_ty], Box::new(closure_ty.clone()));
                    let actual = Type::Fn(param_types, Box::new(closure_ty));
                    let e = TypeErrorEnum::UnexpectedType { expected, actual };
                    return Err(vec![TypeError(e, closure.meta)]);
                }
                let typed_ast::ParamDef(acc_identifier, acc_param_ty) = &params[0];
                let typed_ast::ParamDef(elem_identifier, elem_param_ty) = &params[1];
                coerce_type(&mut init, acc_param_ty)?;
                if &elem_ty != elem_param_ty {
                    let expected = elem_param_ty.clone();
                    let actual = elem_ty;
                    let e = TypeErrorEnum::UnexpectedType { expected, actual };
                    return Err(vec![TypeError(e, closure.meta)]);
                }

                env.push();
                env.set(acc_identifier.clone(), acc_param_ty.clone());
                env.set(elem_identifier.clone(), elem_param_ty.clone());
                let mut body = closure.body.type_check(top_level_defs, env, fns, defs)?;
                unify(&mut init, &mut body, meta)?;
                env.pop();

                let ty = closure_ty;
                coerce_type(&mut body, &ty)?;

                let closure = typed_ast::Closure {
                    ty: ty.clone(),
                    params,
                    body,
                    meta,
                };
                (
                    typed_ast::ExprEnum::Fold(Box::new(arr), Box::new(init), Box::new(closure)),
                    ty,
                )
            }
            ExprEnum::Map(arr, closure) => {
                let arr = arr.type_check(top_level_defs, env, fns, defs)?;
                let typed_ast::Expr(_, array_ty, array_meta) = &arr;
                let (elem_ty, size) = expect_array_type(array_ty, *array_meta)?;
                let closure_ty = closure
                    .ty
                    .as_concrete_type(top_level_defs)
                    .map_err(|e| vec![e])?;
                let mut params = Vec::with_capacity(closure.params.len());
                let mut param_types = Vec::with_capacity(closure.params.len());
                for ParamDef(name, ty) in closure.params.iter() {
                    let ty = ty.as_concrete_type(top_level_defs).map_err(|e| vec![e])?;
                    params.push(typed_ast::ParamDef(name.clone(), ty.clone()));
                    param_types.push(ty);
                }
                if closure.params.len() != 1 {
                    let expected = Type::Fn(vec![elem_ty], Box::new(closure_ty.clone()));
                    let actual = Type::Fn(param_types, Box::new(closure_ty));
                    let e = TypeErrorEnum::UnexpectedType { expected, actual };
                    return Err(vec![TypeError(e, closure.meta)]);
                }
                let typed_ast::ParamDef(elem_identifier, elem_param_ty) = &params[0];
                if &elem_ty != elem_param_ty {
                    let expected = elem_param_ty.clone();
                    let actual = elem_ty;
                    let e = TypeErrorEnum::UnexpectedType { expected, actual };
                    return Err(vec![TypeError(e, closure.meta)]);
                }

                env.push();
                env.set(elem_identifier.clone(), elem_param_ty.clone());
                let mut body = closure.body.type_check(top_level_defs, env, fns, defs)?;
                env.pop();

                coerce_type(&mut body, &closure_ty)?;

                let ty = Type::Array(Box::new(closure_ty.clone()), size);

                let closure = typed_ast::Closure {
                    ty: closure_ty,
                    params,
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
                    return Err(vec![TypeError(e, meta)]);
                }
                let ty = Type::Array(Box::new(Type::Unsigned(UnsignedNumType::Usize)), to - from);
                (typed_ast::ExprEnum::Range(*from, *to), ty)
            }
            ExprEnum::EnumLiteral(identifier, variant) => {
                if let Some(enum_def) = defs.enums.get(identifier.as_str()) {
                    let VariantExpr(variant_name, variant, meta) = variant.as_ref();
                    let meta = *meta;
                    if let Some(types) = enum_def.get(variant_name.as_str()) {
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
                                    return Err(vec![TypeError(e, meta)]);
                                }
                                let mut errors = vec![];
                                let mut exprs = Vec::with_capacity(values.len());
                                for (v, ty) in values.iter().zip(types) {
                                    match v.type_check(top_level_defs, env, fns, defs) {
                                        Ok(mut expr) => {
                                            if let Err(e) = coerce_type(&mut expr, ty) {
                                                errors.extend(e);
                                            }
                                            exprs.push(expr);
                                        }
                                        Err(e) => errors.extend(e),
                                    }
                                }
                                let variant = typed_ast::VariantExpr(
                                    variant_name.to_string(),
                                    typed_ast::VariantExprEnum::Tuple(exprs),
                                    meta,
                                );
                                let ty = Type::Enum(identifier.clone());
                                if errors.is_empty() {
                                    (
                                        typed_ast::ExprEnum::EnumLiteral(
                                            identifier.clone(),
                                            Box::new(variant),
                                        ),
                                        ty,
                                    )
                                } else {
                                    return Err(errors);
                                }
                            }
                            (VariantExprEnum::Unit, Some(_)) => {
                                let e = TypeErrorEnum::ExpectedTupleVariantFoundUnitVariant;
                                return Err(vec![TypeError(e, meta)]);
                            }
                            (VariantExprEnum::Tuple(_), None) => {
                                let e = TypeErrorEnum::ExpectedUnitVariantFoundTupleVariant;
                                return Err(vec![TypeError(e, meta)]);
                            }
                        }
                    } else {
                        let e = TypeErrorEnum::UnknownEnumVariant(
                            identifier.clone(),
                            variant_name.to_string(),
                        );
                        return Err(vec![TypeError(e, meta)]);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownEnum(identifier.clone());
                    return Err(vec![TypeError(e, meta)]);
                }
            }
            ExprEnum::Match(expr, clauses) => {
                let expr = expr.type_check(top_level_defs, env, fns, defs)?;
                let ty = &expr.1;

                match ty {
                    Type::Bool
                    | Type::Unsigned(_)
                    | Type::Signed(_)
                    | Type::Tuple(_)
                    | Type::Struct(_)
                    | Type::Enum(_) => {}
                    Type::Fn(_, _) | Type::Array(_, _) => {
                        let e = TypeErrorEnum::TypeDoesNotSupportPatternMatching(ty.clone());
                        return Err(vec![TypeError(e, meta)]);
                    }
                }

                let mut errors = vec![];
                let mut typed_clauses = Vec::with_capacity(clauses.len());

                for (pattern, expr) in clauses {
                    env.push();
                    let pattern = pattern.type_check(env, fns, defs, ty.clone());
                    let expr = expr.type_check(top_level_defs, env, fns, defs);
                    env.pop();
                    match (pattern, expr) {
                        (Ok(pattern), Ok(expr)) => typed_clauses.push((pattern, expr)),
                        (Ok(_), Err(e)) => errors.extend(e),
                        (Err(e), Ok(_)) => errors.extend(e),
                        (Err(e1), Err(e2)) => {
                            errors.extend(e1);
                            errors.extend(e2);
                        }
                    }
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
                            errors.push(TypeError(e, *meta));
                        }
                    }
                    ret_ty.clone()
                };

                if let Err(e) = check_exhaustiveness(&typed_clauses, ty, defs, meta) {
                    errors.push(e);
                }

                if errors.is_empty() {
                    (
                        typed_ast::ExprEnum::Match(Box::new(expr), typed_clauses),
                        ret_ty,
                    )
                } else {
                    return Err(errors);
                }
            }
            ExprEnum::StructLiteral(name, fields) => {
                if let Some((_, struct_def)) = defs.structs.get(name.as_str()) {
                    let mut errors = vec![];
                    let mut typed_fields = Vec::with_capacity(fields.len());
                    for (field_name, field_value) in fields {
                        if let Some(expected_type) = struct_def.get(field_name.as_str()) {
                            match field_value.type_check(top_level_defs, env, fns, defs) {
                                Ok(mut typed_field) => {
                                    if let Err(e) = coerce_type(&mut typed_field, expected_type) {
                                        errors.extend(e);
                                    }
                                    typed_fields.push((field_name.clone(), typed_field));
                                }
                                Err(e) => errors.extend(e),
                            }
                        } else {
                            let e =
                                TypeErrorEnum::UnknownStructField(name.clone(), field_name.clone());
                            errors.push(TypeError(e, meta));
                        }
                    }
                    if struct_def.len() > fields.len() {
                        for expected_field_name in struct_def.keys() {
                            if !fields.iter().any(|(f, _)| f == expected_field_name) {
                                let e = TypeErrorEnum::MissingStructField(
                                    name.clone(),
                                    expected_field_name.to_string(),
                                );
                                errors.push(TypeError(e, meta));
                            }
                        }
                    }
                    if errors.is_empty() {
                        (
                            typed_ast::ExprEnum::StructLiteral(name.clone(), typed_fields),
                            Type::Struct(name.clone()),
                        )
                    } else {
                        return Err(errors);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownStruct(name.clone());
                    return Err(vec![TypeError(e, meta)]);
                }
            }
            ExprEnum::StructAccess(struct_expr, field) => {
                let struct_expr = struct_expr.type_check(top_level_defs, env, fns, defs)?;
                let name = expect_struct_type(&struct_expr.1, struct_expr.2)?;
                if let Some((_, struct_def)) = defs.structs.get(name.as_str()) {
                    if let Some(field_ty) = struct_def.get(field.as_str()) {
                        (
                            typed_ast::ExprEnum::StructAccess(Box::new(struct_expr), field.clone()),
                            field_ty.clone(),
                        )
                    } else {
                        let e = TypeErrorEnum::UnknownStructField(name.clone(), field.clone());
                        return Err(vec![TypeError(e, meta)]);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownStruct(name.clone());
                    return Err(vec![TypeError(e, meta)]);
                }
            }
        };
        Ok(typed_ast::Expr(expr, ty, meta))
    }
}

impl Pattern {
    fn type_check(
        &self,
        env: &mut Env<Type>,
        fns: &mut TypedFns,
        defs: &Defs,
        ty: Type,
    ) -> Result<typed_ast::Pattern, Vec<TypeError>> {
        let Pattern(pattern, meta) = self;
        let meta = *meta;
        let pattern = match pattern {
            PatternEnum::Identifier(s) => {
                env.set(s.clone(), ty.clone());
                typed_ast::PatternEnum::Identifier(s.clone())
            }
            PatternEnum::True => {
                if ty == Type::Bool {
                    typed_ast::PatternEnum::True
                } else {
                    let e = TypeErrorEnum::UnexpectedType {
                        expected: Type::Bool,
                        actual: ty,
                    };
                    return Err(vec![TypeError(e, meta)]);
                }
            }
            PatternEnum::False => {
                if ty == Type::Bool {
                    typed_ast::PatternEnum::False
                } else {
                    let e = TypeErrorEnum::UnexpectedType {
                        expected: Type::Bool,
                        actual: ty,
                    };
                    return Err(vec![TypeError(e, meta)]);
                }
            }
            PatternEnum::NumUnsigned(n, _) => {
                expect_num_type(&ty, meta)?;
                typed_ast::PatternEnum::NumUnsigned(*n)
            }
            PatternEnum::NumSigned(n, None) if *n >= 0 => {
                expect_num_type(&ty, meta)?;
                typed_ast::PatternEnum::NumSigned(*n)
            }
            PatternEnum::NumSigned(n, _) => {
                expect_signed_num_type(&ty, meta)?;
                typed_ast::PatternEnum::NumSigned(*n)
            }
            PatternEnum::UnsignedInclusiveRange(from, to, _) => {
                expect_num_type(&ty, meta)?;
                typed_ast::PatternEnum::UnsignedInclusiveRange(*from, *to)
            }
            PatternEnum::SignedInclusiveRange(from, to, _) => {
                expect_signed_num_type(&ty, meta)?;
                typed_ast::PatternEnum::SignedInclusiveRange(*from, *to)
            }
            PatternEnum::Tuple(fields) => {
                let field_types = expect_tuple_type(&ty, meta)?;
                if field_types.len() != fields.len() {
                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                        expected: field_types.len(),
                        actual: fields.len(),
                    };
                    return Err(vec![TypeError(e, meta)]);
                }
                let mut errors = vec![];
                let mut typed_fields = Vec::with_capacity(fields.len());
                for (field, ty) in fields.iter().zip(field_types) {
                    match field.type_check(env, fns, defs, ty) {
                        Ok(typed_field) => typed_fields.push(typed_field),
                        Err(e) => errors.extend(e),
                    }
                }
                if errors.is_empty() {
                    typed_ast::PatternEnum::Tuple(typed_fields)
                } else {
                    return Err(errors);
                }
            }
            PatternEnum::Struct(struct_name, fields) => {
                let struct_def_name = expect_struct_type(&ty, meta)?;
                if &struct_def_name != struct_name {
                    let e = TypeErrorEnum::UnexpectedType {
                        expected: ty,
                        actual: Type::Struct(struct_name.clone()),
                    };
                    return Err(vec![TypeError(e, meta)]);
                }
                if let Some((_, struct_def)) = defs.structs.get(struct_def_name.as_str()) {
                    let mut errors = vec![];
                    let mut typed_fields = Vec::with_capacity(fields.len());
                    for (field_name, field_value) in fields {
                        if let Some(field_type) = struct_def.get(field_name.as_str()) {
                            match field_value.type_check(env, fns, defs, field_type.clone()) {
                                Ok(typed_field) => {
                                    typed_fields.push((field_name.clone(), typed_field))
                                }
                                Err(e) => errors.extend(e),
                            }
                        } else {
                            let e = TypeErrorEnum::UnknownStructField(
                                struct_name.clone(),
                                field_name.clone(),
                            );
                            errors.push(TypeError(e, meta));
                        }
                    }
                    if struct_def.len() > fields.len() {
                        for expected_field_name in struct_def.keys() {
                            if !fields.iter().any(|(f, _)| f == expected_field_name) {
                                let e = TypeErrorEnum::MissingStructField(
                                    struct_name.clone(),
                                    expected_field_name.to_string(),
                                );
                                errors.push(TypeError(e, meta));
                            }
                        }
                    }
                    if errors.is_empty() {
                        typed_ast::PatternEnum::Struct(struct_def_name, typed_fields)
                    } else {
                        return Err(errors);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownStruct(struct_def_name.to_string());
                    return Err(vec![TypeError(e, meta)]);
                }
            }
            PatternEnum::EnumUnit(enum_name, variant_name)
            | PatternEnum::EnumTuple(enum_name, variant_name, _) => {
                match &ty {
                    Type::Enum(enum_def_name) if enum_def_name == enum_name => {}
                    _ => {
                        let e = TypeErrorEnum::UnexpectedType {
                            expected: Type::Enum(enum_name.clone()),
                            actual: ty.clone(),
                        };
                        return Err(vec![TypeError(e, meta)]);
                    }
                }
                if let Some(enum_def) = defs.enums.get(enum_name.as_str()) {
                    if let Some(variant) = enum_def.get(variant_name.as_str()) {
                        match (pattern, variant) {
                            (PatternEnum::EnumUnit(_, _), None) => {
                                typed_ast::PatternEnum::EnumUnit(
                                    enum_name.clone(),
                                    variant_name.clone(),
                                )
                            }
                            (PatternEnum::EnumTuple(_, _, fields), Some(field_types)) => {
                                if field_types.len() != fields.len() {
                                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                                        expected: field_types.len(),
                                        actual: fields.len(),
                                    };
                                    return Err(vec![TypeError(e, meta)]);
                                }
                                let mut errors = vec![];
                                let mut typed_fields = Vec::with_capacity(fields.len());
                                for (field, ty) in fields.iter().zip(field_types) {
                                    match field.type_check(env, fns, defs, ty.clone()) {
                                        Ok(typed_field) => typed_fields.push(typed_field),
                                        Err(e) => errors.extend(e),
                                    }
                                }
                                if errors.is_empty() {
                                    typed_ast::PatternEnum::EnumTuple(
                                        enum_name.clone(),
                                        variant_name.clone(),
                                        typed_fields,
                                    )
                                } else {
                                    return Err(errors);
                                }
                            }
                            (PatternEnum::EnumUnit(_, _), Some(_)) => {
                                let e = TypeErrorEnum::ExpectedTupleVariantFoundUnitVariant;
                                return Err(vec![TypeError(e, meta)]);
                            }
                            (PatternEnum::EnumTuple(_, _, _), None) => {
                                let e = TypeErrorEnum::ExpectedUnitVariantFoundTupleVariant;
                                return Err(vec![TypeError(e, meta)]);
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        let e = TypeErrorEnum::UnknownEnumVariant(
                            enum_name.clone(),
                            variant_name.to_string(),
                        );
                        return Err(vec![TypeError(e, meta)]);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownEnum(enum_name.clone());
                    return Err(vec![TypeError(e, meta)]);
                }
            }
        };
        Ok(typed_ast::Pattern(pattern, ty, meta))
    }
}

// Implements the algorithm described at
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/thir/pattern/usefulness/index.html
// (which implements the paper http://moscova.inria.fr/~maranget/papers/warn/index.html)
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
    let witnesses = usefulness(patterns, wildcard_pattern, defs);
    if !witnesses.is_empty() {
        let e = TypeErrorEnum::PatternsAreNotExhaustive(witnesses);
        Err(TypeError(e, meta))
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum Ctor {
    True,
    False,
    UnsignedInclusiveRange(UnsignedNumType, u128, u128),
    SignedInclusiveRange(SignedNumType, i128, i128),
    Tuple(Vec<Type>),
    Struct(String, Vec<(String, Type)>),
    Variant(String, String, Option<Vec<Type>>),
    Array(Box<Type>, usize),
}

type PatternStack = Vec<typed_ast::Pattern>;

fn specialize(ctor: &Ctor, pattern: &[typed_ast::Pattern]) -> Vec<PatternStack> {
    let head = pattern.first().unwrap();
    let tail = pattern.iter().skip(1).cloned();
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
        Ctor::UnsignedInclusiveRange(_, min, max) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => vec![tail.collect()],
            typed_ast::PatternEnum::NumUnsigned(n) if n == min && n == max => vec![tail.collect()],
            typed_ast::PatternEnum::UnsignedInclusiveRange(n_min, n_max)
                if n_min <= min && max <= n_max =>
            {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::SignedInclusiveRange(_, min, max) => match head_enum {
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
                    let p = typed_ast::Pattern(wildcard, ty.clone(), *meta);
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            typed_ast::PatternEnum::Tuple(fields) => {
                vec![fields.iter().cloned().chain(tail).collect()]
            }
            _ => vec![],
        },
        Ctor::Array(_, _) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => vec![tail.collect()],
            _ => vec![],
        },
        Ctor::Struct(struct_name, field_types) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                let mut fields = Vec::with_capacity(field_types.len());
                for (_, ty) in field_types {
                    let wildcard = typed_ast::PatternEnum::Identifier("_".to_string());
                    let p = typed_ast::Pattern(wildcard, ty.clone(), *meta);
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            typed_ast::PatternEnum::Struct(struct_name_in_pattern, fields)
                if struct_name == struct_name_in_pattern =>
            {
                vec![fields
                    .iter()
                    .map(|(_, pattern)| pattern.clone())
                    .chain(tail)
                    .collect()]
            }
            _ => vec![],
        },
        Ctor::Variant(_, v1, fields) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                let field_types = fields.as_deref().unwrap_or_default();
                let mut fields = Vec::with_capacity(field_types.len());
                for ty in field_types {
                    let wildcard = typed_ast::PatternEnum::Identifier("_".to_string());
                    let p = typed_ast::Pattern(wildcard, ty.clone(), *meta);
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            typed_ast::PatternEnum::EnumUnit(_, v2) if v1 == v2 => vec![tail.collect()],
            typed_ast::PatternEnum::EnumTuple(_, v2, fields) if v1 == v2 => {
                vec![fields.iter().cloned().chain(tail).collect()]
            }
            _ => vec![],
        },
    }
}

fn split_unsigned_range(
    ty: UnsignedNumType,
    patterns: &[PatternStack],
    min: u128,
    max: u128,
) -> Vec<Ctor> {
    // TODO: the following does not work correctly for u128::MAX, perhaps u128 types should be
    // removed from the language altogether?
    let mut split_points = vec![min, if max == u128::MAX { max } else { max + 1 }];
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
    split_points.sort_unstable();
    split_points.dedup();
    let mut ranges = vec![];
    for range in split_points.windows(2) {
        if range[0] < range[1] - 1 {
            ranges.push(Ctor::UnsignedInclusiveRange(ty, range[0], range[0]));
        }
        if range[0] >= min && range[1] - 1 <= max {
            if range[0] < range[1] - 1 {
                ranges.push(Ctor::UnsignedInclusiveRange(ty, range[0] + 1, range[1] - 1));
            } else {
                ranges.push(Ctor::UnsignedInclusiveRange(ty, range[0], range[1] - 1));
            }
        }
    }
    ranges
}

fn split_signed_range(
    ty: SignedNumType,
    patterns: &[PatternStack],
    min: i128,
    max: i128,
) -> Vec<Ctor> {
    // TODO: the following does not work correctly for i128::MAX, perhaps i128 types should be
    // removed from the language altogether?
    let mut split_points = vec![min, if max == i128::MAX { max } else { max + 1 }];
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
    split_points.sort_unstable();
    split_points.dedup();
    let mut ranges = vec![];
    for range in split_points.windows(2) {
        if range[0] < range[1] - 1 {
            ranges.push(Ctor::SignedInclusiveRange(ty, range[0], range[0]));
        }
        if range[0] >= min && range[1] - 1 <= max {
            ranges.push(Ctor::SignedInclusiveRange(ty, range[0], range[1] - 1));
        }
    }
    ranges
}

fn split_ctor(patterns: &[PatternStack], q: &[typed_ast::Pattern], defs: &Defs) -> Vec<Ctor> {
    let head = q.first().unwrap();
    let typed_ast::Pattern(head_enum, ty, _) = head;
    match ty {
        Type::Bool => vec![Ctor::True, Ctor::False],
        Type::Unsigned(ty) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                split_unsigned_range(*ty, patterns, 0, ty.max())
            }
            typed_ast::PatternEnum::NumUnsigned(n) => {
                vec![Ctor::UnsignedInclusiveRange(*ty, *n, *n)]
            }
            typed_ast::PatternEnum::UnsignedInclusiveRange(min, max) => {
                split_unsigned_range(*ty, patterns, *min, *max)
            }
            _ => panic!("cannot split {:?} for type {:?}", head_enum, ty),
        },
        Type::Signed(ty) => match head_enum {
            typed_ast::PatternEnum::Identifier(_) => {
                vec![Ctor::SignedInclusiveRange(*ty, ty.min(), ty.max())]
            }
            typed_ast::PatternEnum::NumUnsigned(n) => {
                vec![Ctor::SignedInclusiveRange(*ty, *n as i128, *n as i128)]
            }
            typed_ast::PatternEnum::NumSigned(n) => vec![Ctor::SignedInclusiveRange(*ty, *n, *n)],
            typed_ast::PatternEnum::UnsignedInclusiveRange(min, max) => {
                split_signed_range(*ty, patterns, *min as i128, *max as i128)
            }
            typed_ast::PatternEnum::SignedInclusiveRange(min, max) => {
                split_signed_range(*ty, patterns, *min, *max)
            }
            _ => panic!("cannot split {:?} for type {:?}", head_enum, ty),
        },
        Type::Struct(struct_name) => {
            let (fields, field_types) = defs.structs.get(struct_name.as_str()).unwrap();
            let mut typed_fields = Vec::with_capacity(fields.len());
            for field in fields {
                typed_fields.push((field.to_string(), field_types.get(field).unwrap().clone()));
            }
            vec![Ctor::Struct(struct_name.clone(), typed_fields)]
        }
        Type::Enum(enum_name) => {
            let variants = defs.enums.get(enum_name.as_str()).unwrap();
            variants
                .iter()
                .map(|(name, fields)| {
                    Ctor::Variant(enum_name.clone(), name.to_string(), fields.clone())
                })
                .collect()
        }
        Type::Tuple(fields) => {
            vec![Ctor::Tuple(fields.clone())]
        }
        Type::Array(elem_ty, size) => vec![Ctor::Array(elem_ty.clone(), *size)],
        Type::Fn(_, _) => {
            panic!("Type {:?} does not support pattern matching", ty)
        }
    }
}

fn usefulness(patterns: Vec<PatternStack>, q: PatternStack, defs: &Defs) -> Vec<PatternStack> {
    if patterns.is_empty() {
        vec![q]
    } else if patterns[0].is_empty() || q.is_empty() {
        vec![]
    } else {
        let mut witnesses = vec![];
        let meta = MetaInfo {
            start: (0, 0),
            end: (0, 0),
        };
        for ctor in split_ctor(&patterns, &q, defs) {
            let mut specialized = Vec::new();
            for p in patterns.iter() {
                let pattern_specialized = specialize(&ctor, p);
                specialized.extend(pattern_specialized);
            }
            for q in specialize(&ctor, &q) {
                for mut witness in usefulness(specialized.clone(), q.clone(), defs) {
                    match &ctor {
                        Ctor::True => witness.insert(
                            0,
                            typed_ast::Pattern(typed_ast::PatternEnum::True, Type::Bool, meta),
                        ),
                        Ctor::False => witness.insert(
                            0,
                            typed_ast::Pattern(typed_ast::PatternEnum::False, Type::Bool, meta),
                        ),
                        Ctor::UnsignedInclusiveRange(ty, min, max) => witness.insert(
                            0,
                            typed_ast::Pattern(
                                typed_ast::PatternEnum::UnsignedInclusiveRange(*min, *max),
                                Type::Unsigned(*ty),
                                meta,
                            ),
                        ),
                        Ctor::SignedInclusiveRange(ty, min, max) => witness.insert(
                            0,
                            typed_ast::Pattern(
                                typed_ast::PatternEnum::SignedInclusiveRange(*min, *max),
                                Type::Signed(*ty),
                                meta,
                            ),
                        ),
                        Ctor::Tuple(fields) => {
                            witness = vec![typed_ast::Pattern(
                                typed_ast::PatternEnum::Tuple(witness),
                                Type::Tuple(fields.clone()),
                                meta,
                            )]
                        }
                        Ctor::Struct(struct_name, fields) => {
                            let witness_fields: Vec<_> = fields
                                .iter()
                                .zip(witness.into_iter())
                                .map(|((field_name, _), pattern)| (field_name.clone(), pattern))
                                .collect();
                            witness = vec![typed_ast::Pattern(
                                typed_ast::PatternEnum::Struct(struct_name.clone(), witness_fields),
                                Type::Struct(struct_name.clone()),
                                meta,
                            )]
                        }
                        Ctor::Variant(enum_name, variant_name, None) => {
                            witness = vec![typed_ast::Pattern(
                                typed_ast::PatternEnum::EnumUnit(
                                    enum_name.clone(),
                                    variant_name.clone(),
                                ),
                                Type::Enum(enum_name.clone()),
                                meta,
                            )]
                        }
                        Ctor::Variant(enum_name, variant_name, Some(_)) => {
                            witness = vec![typed_ast::Pattern(
                                typed_ast::PatternEnum::EnumTuple(
                                    enum_name.clone(),
                                    variant_name.clone(),
                                    witness,
                                ),
                                Type::Enum(enum_name.clone()),
                                meta,
                            )]
                        }
                        Ctor::Array(elem_ty, size) => witness.insert(
                            0,
                            typed_ast::Pattern(
                                typed_ast::PatternEnum::Identifier("_".to_string()),
                                Type::Array(elem_ty.clone(), *size),
                                meta,
                            ),
                        ),
                    }
                    witnesses.push(witness);
                }
            }
        }
        witnesses
    }
}

fn expect_array_type(ty: &Type, meta: MetaInfo) -> Result<(Type, usize), Vec<TypeError>> {
    match ty {
        Type::Array(elem, size) => Ok((*elem.clone(), *size)),
        _ => Err(vec![TypeError(
            TypeErrorEnum::ExpectedArrayType(ty.clone()),
            meta,
        )]),
    }
}

fn expect_struct_type(ty: &Type, meta: MetaInfo) -> Result<String, Vec<TypeError>> {
    match ty {
        Type::Struct(name) => Ok(name.clone()),
        _ => Err(vec![TypeError(
            TypeErrorEnum::ExpectedStructType(ty.clone()),
            meta,
        )]),
    }
}

fn expect_tuple_type(ty: &Type, meta: MetaInfo) -> Result<Vec<Type>, Vec<TypeError>> {
    match ty {
        Type::Tuple(types) => Ok(types.clone()),
        _ => Err(vec![TypeError(
            TypeErrorEnum::ExpectedTupleType(ty.clone()),
            meta,
        )]),
    }
}

fn expect_num_type(ty: &Type, meta: MetaInfo) -> Result<(), Vec<TypeError>> {
    match ty {
        Type::Unsigned(_) | Type::Signed(_) => Ok(()),
        _ => Err(vec![TypeError(
            TypeErrorEnum::ExpectedNumberType(ty.clone()),
            meta,
        )]),
    }
}

fn expect_signed_num_type(ty: &Type, meta: MetaInfo) -> Result<(), Vec<TypeError>> {
    match ty {
        Type::Signed(_) => Ok(()),
        _ => Err(vec![TypeError(
            TypeErrorEnum::ExpectedSignedNumberType(ty.clone()),
            meta,
        )]),
    }
}

fn expect_bool_or_num_type(ty: &Type, meta: MetaInfo) -> Result<(), Vec<TypeError>> {
    if let Type::Bool = ty {
        return Ok(());
    };
    if let Ok(()) = expect_num_type(ty, meta) {
        return Ok(());
    }
    Err(vec![TypeError(
        TypeErrorEnum::ExpectedBoolOrNumberType(ty.clone()),
        meta,
    )])
}

pub(crate) fn coerce_type(
    expr: &mut typed_ast::Expr,
    expected: &Type,
) -> Result<(), Vec<TypeError>> {
    let typed_ast::Expr(expr_enum, actual, meta) = &expr;
    let actual = actual.clone();
    if let typed_ast::ExprEnum::NumUnsigned(n, None) = expr_enum {
        if is_coercible_unsigned(*n, expected) {
            expr.1 = expected.clone();
            return Ok(());
        }
    }
    if let typed_ast::ExprEnum::NumSigned(n, None) = expr_enum {
        if is_coercible_signed(*n, expected) {
            expr.1 = expected.clone();
            return Ok(());
        }
    }
    if &actual == expected {
        Ok(())
    } else {
        let expected = expected.clone();
        let e = TypeErrorEnum::UnexpectedType { expected, actual };
        Err(vec![TypeError(e, *meta)])
    }
}

fn unify(
    e1: &mut typed_ast::Expr,
    e2: &mut typed_ast::Expr,
    m: MetaInfo,
) -> Result<Type, Vec<TypeError>> {
    let typed_ast::Expr(expr1, ty1, meta1) = e1;
    let typed_ast::Expr(expr2, ty2, meta2) = e2;
    let ty = match (expr1, expr2) {
        (typed_ast::ExprEnum::NumUnsigned(n, None), _) if is_coercible_unsigned(*n, ty2) => {
            Ok(ty2.clone())
        }
        (_, typed_ast::ExprEnum::NumUnsigned(n, None)) if is_coercible_unsigned(*n, ty1) => {
            Ok(ty1.clone())
        }
        (typed_ast::ExprEnum::NumSigned(n, None), _) if is_coercible_signed(*n, ty2) => {
            Ok(ty2.clone())
        }
        (_, typed_ast::ExprEnum::NumSigned(n, None)) if is_coercible_signed(*n, ty1) => {
            Ok(ty1.clone())
        }
        _ if *ty1 == *ty2 => Ok(ty1.clone()),
        _ => {
            let e = TypeErrorEnum::TypeMismatch((ty1.clone(), *meta1), (ty2.clone(), *meta2));
            Err(vec![TypeError(e, m)])
        }
    };
    if let Ok(ty) = &ty {
        e1.1 = ty.clone();
        e2.1 = ty.clone();
    }
    ty
}

fn is_coercible_unsigned(n: u128, ty: &Type) -> bool {
    if let Type::Unsigned(ty) = ty {
        match ty {
            UnsignedNumType::Usize => n <= usize::MAX as u128,
            UnsignedNumType::U8 => n <= u8::MAX as u128,
            UnsignedNumType::U16 => n <= u16::MAX as u128,
            UnsignedNumType::U32 => n <= u32::MAX as u128,
            UnsignedNumType::U64 => n <= u64::MAX as u128,
            UnsignedNumType::U128 => true,
        }
    } else if let Type::Signed(ty) = ty {
        match ty {
            SignedNumType::I8 => n <= i8::MAX as u128,
            SignedNumType::I16 => n <= i16::MAX as u128,
            SignedNumType::I32 => n <= i32::MAX as u128,
            SignedNumType::I64 => n <= i64::MAX as u128,
            SignedNumType::I128 => n <= i128::MAX as u128,
        }
    } else {
        false
    }
}

fn is_coercible_signed(n: i128, ty: &Type) -> bool {
    match ty {
        Type::Bool => false,
        Type::Unsigned(_) => {
            if n < 0 {
                false
            } else {
                is_coercible_unsigned(n as u128, ty)
            }
        }
        Type::Signed(SignedNumType::I8) => n >= i8::MIN as i128 && n <= i8::MAX as i128,
        Type::Signed(SignedNumType::I16) => n >= i16::MIN as i128 && n <= i16::MAX as i128,
        Type::Signed(SignedNumType::I32) => n >= i32::MIN as i128 && n <= i32::MAX as i128,
        Type::Signed(SignedNumType::I64) => n >= i64::MIN as i128 && n <= i64::MAX as i128,
        Type::Signed(SignedNumType::I128) => true,
        Type::Fn(_, _) => false,
        Type::Array(_, _) => false,
        Type::Tuple(_) => false,
        Type::Struct(_) => false,
        Type::Enum(_) => false,
    }
}
