//! Type-checker, transforming an untyped [`crate::ast::Program`] into a typed
//! [`crate::ast::Program`].

use std::collections::{HashMap, HashSet};

use crate::{
    ast::{
        self, Accessor, ConstDef, ConstExpr, ConstExprEnum, EnumDef, Expr, ExprEnum, Mutability,
        Op, ParamDef, Pattern, PatternEnum, Stmt, StmtEnum, StructDef, Type, UnaryOp, Variant,
        VariantExprEnum,
    },
    env::Env,
    token::{MetaInfo, SignedNumType, UnsignedNumType},
    TypedExpr, TypedFnDef, TypedPattern, TypedProgram, TypedStmt, UntypedExpr, UntypedFnDef,
    UntypedPattern, UntypedProgram, UntypedStmt,
};

/// An error found during type-checking, with its location in the source code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeError(pub TypeErrorEnum, pub MetaInfo);

impl PartialOrd for TypeError {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
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
    UnknownEnum(String, String),
    /// The enum exists, but no variant declaration with the specified name was found.
    UnknownEnumVariant(String, String),
    /// No variable or function with the specified name exists in the current scope.
    UnknownIdentifier(String),
    /// The identifier exists, but it was declared as immutable.
    IdentifierNotDeclaredAsMutable(String),
    /// The index is larger than the specified tuple size.
    TupleAccessOutOfBounds(usize),
    /// A parameter name is used more than once in a function declaration.
    DuplicateFnParam(String),
    /// An Boolean or number expression was expected.
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
    TypeMismatch(Type, Type),
    /// The specified range has invalid min or max values.
    InvalidRange(u64, u64),
    /// The specified pattern does not match the type of the matched expression.
    PatternDoesNotMatchType(Type),
    /// The patterns do not cover all possible cases.
    PatternsAreNotExhaustive(Vec<PatternStack>),
    /// The expression cannot be matched upon.
    TypeDoesNotSupportPatternMatching(Type),
    /// The specified identifier is not a constant.
    ArraySizeNotConst(String),
    /// The specified expression is not a literal usize number.
    UsizeNotLiteral,
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
            TypeErrorEnum::UnknownEnum(enum_name, enum_variant) => {
                f.write_fmt(format_args!("Unknown enum '{enum_name}::{enum_variant}'"))
            }
            TypeErrorEnum::UnknownEnumVariant(enum_name, enum_variant) => f.write_fmt(
                format_args!("Unknown enum variant '{enum_name}::{enum_variant}'"),
            ),
            TypeErrorEnum::UnknownIdentifier(name) => {
                f.write_fmt(format_args!("Unknown identifier '{name}'"))
            }
            TypeErrorEnum::IdentifierNotDeclaredAsMutable(name) => {
                f.write_fmt(format_args!("'{name}' exists, but was not declared as mutable"))
            }
            TypeErrorEnum::TupleAccessOutOfBounds(size) => {
                f.write_fmt(format_args!("The tuple only has {size} fields"))
            }
            TypeErrorEnum::DuplicateFnParam(name) => f.write_fmt(format_args!(
                "The function parameter '{name}' is declared multiple times"
            )),
            TypeErrorEnum::ExpectedBoolOrNumberType(ty) => f.write_fmt(format_args!(
                "Expected a Boolean or number type, but found {ty}"
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
            TypeErrorEnum::TypeMismatch(x, y) => f.write_fmt(format_args!(
                "The arguments have incompatible types; {x} vs {y}"
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
            TypeErrorEnum::ArraySizeNotConst(identifier) => {
                f.write_fmt(format_args!("Array sizes must be constants, but '{identifier}' is a variable"))
            }
            TypeErrorEnum::UsizeNotLiteral => {
                f.write_str("Expected a usize number literal")
            }
        }
    }
}

type TypeErrors = Vec<Option<TypeError>>;

pub(crate) struct TopLevelTypes<'a> {
    pub(crate) struct_names: HashSet<&'a String>,
    pub(crate) enum_names: HashSet<&'a String>,
}

impl Type {
    fn as_concrete_type(&self, types: &TopLevelTypes) -> Result<Type, TypeErrors> {
        let ty = match self {
            Type::Bool => Type::Bool,
            Type::Unsigned(n) => Type::Unsigned(*n),
            Type::Signed(n) => Type::Signed(*n),
            Type::Fn(args, ret) => {
                let mut concrete_args = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    concrete_args.push(arg.as_concrete_type(types)?);
                }
                let ret = ret.as_concrete_type(types)?;
                Type::Fn(concrete_args, Box::new(ret))
            }
            Type::Array(elem, size) => {
                let elem = elem.as_concrete_type(types)?;
                Type::Array(Box::new(elem), *size)
            }
            Type::ArrayConst(elem, size) => {
                let elem = elem.as_concrete_type(types)?;
                Type::ArrayConst(Box::new(elem), size.clone())
            }
            Type::Tuple(fields) => {
                let mut concrete_fields = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    concrete_fields.push(field.as_concrete_type(types)?);
                }
                Type::Tuple(concrete_fields)
            }
            Type::UntypedTopLevelDefinition(name, meta) => {
                if types.struct_names.contains(name) {
                    Type::Struct(name.clone())
                } else if types.enum_names.contains(name) {
                    Type::Enum(name.clone())
                } else {
                    let e = TypeErrorEnum::UnknownStructOrEnum(name.clone());
                    return Err(vec![Some(TypeError(e, *meta))]);
                }
            }
            Type::Struct(name) => Type::Struct(name.clone()),
            Type::Enum(name) => Type::Enum(name.clone()),
        };
        Ok(ty)
    }
}

/// Static top-level definitions of enums and functions.
pub struct Defs<'a> {
    consts: HashMap<&'a str, &'a Type>,
    structs: HashMap<&'a str, (Vec<&'a str>, HashMap<&'a str, Type>)>,
    enums: HashMap<&'a str, HashMap<&'a str, Option<Vec<Type>>>>,
    fns: HashMap<&'a str, &'a UntypedFnDef>,
}

impl<'a> Defs<'a> {
    pub(crate) fn new(
        const_defs: &'a HashMap<String, Type>,
        struct_defs: &'a HashMap<String, StructDef>,
        enum_defs: &'a HashMap<String, EnumDef>,
    ) -> Self {
        let mut defs = Self {
            consts: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            fns: HashMap::new(),
        };
        for (const_name, ty) in const_defs.iter() {
            defs.consts.insert(const_name, ty);
        }
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
    typed: HashMap<String, Result<TypedFnDef, TypeErrors>>,
}

impl TypedFns {
    pub(crate) fn new() -> Self {
        Self {
            currently_being_checked: HashSet::new(),
            typed: HashMap::new(),
        }
    }
}

impl UntypedProgram {
    /// Type-checks the parsed program, returning either a typed AST or type errors.
    pub fn type_check(&self) -> Result<TypedProgram, Vec<TypeError>> {
        let mut errors = vec![];
        let mut struct_names = HashSet::with_capacity(self.struct_defs.len());
        let mut enum_names = HashSet::with_capacity(self.enum_defs.len());
        struct_names.extend(self.struct_defs.keys());
        enum_names.extend(self.enum_defs.keys());
        let top_level_defs = TopLevelTypes {
            struct_names,
            enum_names,
        };
        let mut const_deps: HashMap<String, HashMap<String, (Type, MetaInfo)>> = HashMap::new();
        let mut const_types = HashMap::with_capacity(self.const_defs.len());
        let mut const_defs = HashMap::with_capacity(self.const_defs.len());
        {
            for (const_name, const_def) in self.const_defs.iter() {
                fn check_const_expr(
                    value: &ConstExpr,
                    const_def: &ConstDef,
                    errors: &mut Vec<Option<TypeError>>,
                    const_deps: &mut HashMap<String, HashMap<String, (Type, MetaInfo)>>,
                ) {
                    let ConstExpr(value, meta) = value;
                    let meta = *meta;
                    match value {
                        ConstExprEnum::True | ConstExprEnum::False => {
                            if const_def.ty != Type::Bool {
                                let e = TypeErrorEnum::UnexpectedType {
                                    expected: const_def.ty.clone(),
                                    actual: Type::Bool,
                                };
                                errors.extend(vec![Some(TypeError(e, meta))]);
                            }
                        }
                        ConstExprEnum::NumUnsigned(_, ty) => {
                            let ty = Type::Unsigned(*ty);
                            if const_def.ty != ty {
                                let e = TypeErrorEnum::UnexpectedType {
                                    expected: const_def.ty.clone(),
                                    actual: ty,
                                };
                                errors.extend(vec![Some(TypeError(e, meta))]);
                            }
                        }
                        ConstExprEnum::NumSigned(_, ty) => {
                            let ty = Type::Signed(*ty);
                            if const_def.ty != ty {
                                let e = TypeErrorEnum::UnexpectedType {
                                    expected: const_def.ty.clone(),
                                    actual: ty,
                                };
                                errors.extend(vec![Some(TypeError(e, meta))]);
                            }
                        }
                        ConstExprEnum::ExternalValue { party, identifier } => {
                            const_deps
                                .entry(party.clone())
                                .or_default()
                                .insert(identifier.clone(), (const_def.ty.clone(), meta));
                        }
                        ConstExprEnum::Max(args) | ConstExprEnum::Min(args) => {
                            for arg in args {
                                check_const_expr(arg, const_def, errors, const_deps);
                            }
                        }
                    }
                }
                check_const_expr(&const_def.value, const_def, &mut errors, &mut const_deps);
                const_defs.insert(const_name.clone(), const_def.clone());
                const_types.insert(const_name.clone(), const_def.ty.clone());
            }
        }
        let mut struct_defs = HashMap::with_capacity(self.struct_defs.len());
        for (struct_name, struct_def) in self.struct_defs.iter() {
            let meta = struct_def.meta;
            let mut fields = Vec::with_capacity(struct_def.fields.len());
            for (name, ty) in struct_def.fields.iter() {
                match ty.as_concrete_type(&top_level_defs) {
                    Ok(ty) => fields.push((name.clone(), ty)),
                    Err(e) => errors.extend(e),
                }
            }
            struct_defs.insert(struct_name.clone(), StructDef { fields, meta });
        }
        let mut enum_defs = HashMap::with_capacity(self.enum_defs.len());
        for (enum_name, enum_def) in self.enum_defs.iter() {
            let meta = enum_def.meta;
            let mut variants = Vec::with_capacity(enum_def.variants.len());
            for variant in enum_def.variants.iter() {
                variants.push(match variant {
                    Variant::Unit(variant_name) => Variant::Unit(variant_name.clone()),
                    Variant::Tuple(variant_name, variant_fields) => {
                        let mut fields = Vec::with_capacity(variant_fields.len());
                        for field in variant_fields.iter() {
                            match field.as_concrete_type(&top_level_defs) {
                                Ok(field) => fields.push(field),
                                Err(e) => errors.extend(e),
                            }
                        }
                        Variant::Tuple(variant_name.clone(), fields)
                    }
                });
            }
            enum_defs.insert(enum_name.clone(), EnumDef { variants, meta });
        }

        let mut untyped_defs = Defs::new(&const_types, &struct_defs, &enum_defs);
        let mut checked_fn_defs = TypedFns::new();
        for (fn_name, fn_def) in self.fn_defs.iter() {
            untyped_defs.fns.insert(fn_name, fn_def);
        }
        for (fn_name, fn_def) in self.fn_defs.iter() {
            if fn_def.is_pub {
                if fn_def.params.is_empty() {
                    let e = TypeErrorEnum::PubFnWithoutParams(fn_name.clone());
                    errors.push(Some(TypeError(e, fn_def.meta)));
                } else {
                    let typed_fn =
                        fn_def.type_check(&top_level_defs, &mut checked_fn_defs, &untyped_defs);
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
                errors.push(Some(TypeError(e, fn_def.meta)));
            }
        }
        let mut fn_defs = HashMap::new();
        for (fn_name, fn_def) in checked_fn_defs.typed.into_iter() {
            if let Ok(fn_def) = fn_def {
                fn_defs.insert(fn_name, fn_def);
            }
        }
        if errors.is_empty() {
            Ok(TypedProgram {
                const_deps,
                const_defs,
                struct_defs,
                enum_defs,
                fn_defs,
            })
        } else {
            let mut errors: Vec<TypeError> = errors.into_iter().flatten().collect();
            errors.sort();
            Err(errors)
        }
    }
}

impl UntypedFnDef {
    fn type_check(
        &self,
        top_level_defs: &TopLevelTypes,
        fns: &mut TypedFns,
        defs: &Defs,
    ) -> Result<TypedFnDef, TypeErrors> {
        if fns.currently_being_checked.contains(&self.identifier) {
            let e = TypeErrorEnum::RecursiveFnDef(self.identifier.clone());
            return Err(vec![Some(TypeError(e, self.meta))]);
        } else {
            fns.currently_being_checked.insert(self.identifier.clone());
        }
        let mut errors = vec![];
        let mut env = Env::new();
        env.push();
        let mut params = Vec::with_capacity(self.params.len());
        let mut param_identifiers = HashSet::new();
        for param in self.params.iter() {
            if param_identifiers.contains(&param.name) {
                let e = TypeErrorEnum::DuplicateFnParam(param.name.clone());
                errors.push(Some(TypeError(e, self.meta)));
            } else {
                param_identifiers.insert(param.name.clone());
            }
            match param.ty.as_concrete_type(top_level_defs) {
                Ok(ty) => {
                    env.let_in_current_scope(
                        param.name.clone(),
                        (Some(ty.clone()), param.mutability),
                    );
                    params.push(ParamDef {
                        mutability: param.mutability,
                        name: param.name.clone(),
                        ty,
                    });
                }
                Err(e) => {
                    env.let_in_current_scope(param.name.clone(), (None, param.mutability));
                    errors.extend(e);
                }
            }
        }

        let body = type_check_block(&self.body, top_level_defs, &mut env, fns, defs);
        fns.currently_being_checked.remove(&self.identifier);
        env.pop();

        match body {
            Ok((mut body, _)) => match self.ty.as_concrete_type(top_level_defs) {
                Ok(ret_ty) => {
                    if let Some(StmtEnum::Expr(ret_expr)) = body.last_mut().map(|s| &mut s.inner) {
                        if let Err(e) = check_type(ret_expr, &ret_ty) {
                            errors.extend(e);
                        }
                    } else if ret_ty != Type::Tuple(vec![]) {
                        let e = TypeErrorEnum::UnexpectedType {
                            expected: ret_ty.clone(),
                            actual: Type::Tuple(vec![]),
                        };
                        errors.push(Some(TypeError(e, self.meta)));
                    }
                    if errors.is_empty() {
                        Ok(TypedFnDef {
                            is_pub: self.is_pub,
                            identifier: self.identifier.clone(),
                            params,
                            ty: ret_ty,
                            body,
                            meta: self.meta,
                        })
                    } else {
                        Err(errors)
                    }
                }
                Err(e) => {
                    errors.extend(e);
                    Err(errors)
                }
            },
            Err(e) => {
                errors.extend(e);
                Err(errors)
            }
        }
    }
}

fn type_check_block(
    block: &[UntypedStmt],
    top_level_defs: &TopLevelTypes,
    env: &mut Env<(Option<Type>, Mutability)>,
    fns: &mut TypedFns,
    defs: &Defs,
) -> Result<(Vec<TypedStmt>, Type), TypeErrors> {
    let mut typed_block = Vec::with_capacity(block.len());
    let mut ret_ty = Type::Tuple(vec![]);
    let mut errors = vec![];
    for (i, stmt) in block.iter().enumerate() {
        match stmt.type_check(top_level_defs, env, fns, defs) {
            Ok(stmt) => {
                if i == block.len() - 1 {
                    if let StmtEnum::Expr(expr) = &stmt.inner {
                        ret_ty = expr.ty.clone();
                    }
                }
                typed_block.push(stmt);
            }
            Err(e) => {
                errors.extend(e);
            }
        }
    }
    if errors.is_empty() {
        Ok((typed_block, ret_ty))
    } else {
        Err(errors)
    }
}

impl UntypedStmt {
    pub(crate) fn type_check(
        &self,
        top_level_defs: &TopLevelTypes,
        env: &mut Env<(Option<Type>, Mutability)>,
        fns: &mut TypedFns,
        defs: &Defs,
    ) -> Result<TypedStmt, TypeErrors> {
        let meta = self.meta;
        match &self.inner {
            ast::StmtEnum::Let(pattern, ty, binding) => {
                match binding.type_check(top_level_defs, env, fns, defs) {
                    Ok(mut binding) => {
                        if let Some(ty) = ty {
                            let ty = ty.as_concrete_type(top_level_defs)?;
                            check_type(&mut binding, &ty)?;
                        }
                        let pattern =
                            pattern.type_check(env, fns, defs, Some(binding.ty.clone()))?;
                        Ok(Stmt::new(StmtEnum::Let(pattern, ty.clone(), binding), meta))
                    }
                    Err(mut errors) => {
                        if let Err(e) = pattern.type_check(env, fns, defs, None) {
                            errors.extend(e);
                        }
                        Err(errors)
                    }
                }
            }
            ast::StmtEnum::LetMut(identifier, ty, binding) => {
                match binding.type_check(top_level_defs, env, fns, defs) {
                    Ok(mut binding) => {
                        if let Some(ty) = ty {
                            let ty = ty.as_concrete_type(top_level_defs)?;
                            check_type(&mut binding, &ty)?;
                        }
                        if binding.ty == Type::Unsigned(UnsignedNumType::Unspecified)
                            || binding.ty == Type::Signed(SignedNumType::Unspecified)
                        {
                            check_or_constrain_signed(&mut binding, SignedNumType::I32)?;
                        }
                        if let Type::Array(ty, _) | Type::ArrayConst(ty, _) = &mut binding.ty {
                            if let Type::Unsigned(UnsignedNumType::Unspecified)
                            | Type::Signed(SignedNumType::Unspecified) = ty.as_ref()
                            {
                                *ty = Box::new(Type::Signed(SignedNumType::I32));
                            }
                        }
                        env.let_in_current_scope(
                            identifier.clone(),
                            (Some(binding.ty.clone()), Mutability::Mutable),
                        );
                        Ok(Stmt::new(
                            StmtEnum::LetMut(identifier.clone(), ty.clone(), binding),
                            meta,
                        ))
                    }
                    Err(e) => {
                        env.let_in_current_scope(identifier.clone(), (None, Mutability::Mutable));
                        Err(e)
                    }
                }
            }
            ast::StmtEnum::Expr(expr) => {
                let expr = expr.type_check(top_level_defs, env, fns, defs)?;
                Ok(Stmt::new(StmtEnum::Expr(expr), meta))
            }
            ast::StmtEnum::VarAssign(identifier, accessors, value) => {
                match env.get(identifier) {
                    Some((Some(mut elem_ty), Mutability::Mutable)) => {
                        let mut typed_accessors = vec![];
                        for (access, meta) in accessors {
                            let typed = match access {
                                Accessor::ArrayAccess { index, .. } => {
                                    let array_ty = elem_ty.clone();
                                    elem_ty = expect_array_type(&elem_ty, *meta)?;

                                    let mut index =
                                        index.type_check(top_level_defs, env, fns, defs)?;
                                    check_or_constrain_unsigned(
                                        &mut index,
                                        UnsignedNumType::Usize,
                                    )?;
                                    Accessor::ArrayAccess { array_ty, index }
                                }
                                Accessor::TupleAccess { index, .. } => {
                                    let value_types = expect_tuple_type(&elem_ty, *meta)?;
                                    if *index < value_types.len() {
                                        elem_ty = value_types[*index].clone();
                                        Accessor::TupleAccess {
                                            tuple_ty: elem_ty.clone(),
                                            index: *index,
                                        }
                                    } else {
                                        let e = TypeErrorEnum::TupleAccessOutOfBounds(
                                            value_types.len(),
                                        );
                                        return Err(vec![Some(TypeError(e, *meta))]);
                                    }
                                }
                                Accessor::StructAccess { field, .. } => {
                                    let name = expect_struct_type(&elem_ty, *meta)?;
                                    if let Some((_, struct_def)) = defs.structs.get(name.as_str()) {
                                        if let Some(field_ty) = struct_def.get(field.as_str()) {
                                            elem_ty = field_ty.clone();
                                            Accessor::StructAccess {
                                                struct_ty: elem_ty.clone(),
                                                field: field.clone(),
                                            }
                                        } else {
                                            let e = TypeErrorEnum::UnknownStructField(
                                                name.clone(),
                                                field.clone(),
                                            );
                                            return Err(vec![Some(TypeError(e, *meta))]);
                                        }
                                    } else {
                                        let e = TypeErrorEnum::UnknownStruct(name.clone());
                                        return Err(vec![Some(TypeError(e, *meta))]);
                                    }
                                }
                            };
                            typed_accessors.push((typed, *meta));
                        }
                        let mut value = value.type_check(top_level_defs, env, fns, defs)?;
                        check_type(&mut value, &elem_ty)?;
                        Ok(Stmt::new(
                            StmtEnum::VarAssign(identifier.clone(), typed_accessors, value),
                            meta,
                        ))
                    }
                    Some((None, Mutability::Mutable)) => {
                        // binding does not have a type, must have been caused by a previous error, so
                        // just ignore the statement here
                        Err(vec![None])
                    }
                    Some((_, Mutability::Immutable)) => Err(vec![Some(TypeError(
                        TypeErrorEnum::IdentifierNotDeclaredAsMutable(identifier.clone()),
                        meta,
                    ))]),
                    None => Err(vec![Some(TypeError(
                        TypeErrorEnum::UnknownIdentifier(identifier.clone()),
                        meta,
                    ))]),
                }
            }
            ast::StmtEnum::ForEachLoop(pattern, binding, body) => match &binding.inner {
                ExprEnum::FnCall(identifier, args) if identifier == "join" => {
                    let mut errors = vec![];
                    if args.len() != 2 {
                        let e = TypeErrorEnum::WrongNumberOfArgs {
                            expected: 2,
                            actual: args.len(),
                        };
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                    let a = args[0].type_check(top_level_defs, env, fns, defs)?;
                    let (ty_a, meta_a) = match &a.ty {
                        Type::Array(_, _) | Type::ArrayConst(_, _) => (a.ty.clone(), a.meta),
                        ty => {
                            errors.push(Some(TypeError(
                                TypeErrorEnum::ExpectedArrayType(ty.clone()),
                                a.meta,
                            )));
                            (ty.clone(), a.meta)
                        }
                    };
                    let b = args[1].type_check(top_level_defs, env, fns, defs)?;
                    let (ty_b, meta_b) = match &b.ty {
                        Type::Array(_, _) | Type::ArrayConst(_, _) => (b.ty.clone(), b.meta),
                        ty => {
                            errors.push(Some(TypeError(
                                TypeErrorEnum::ExpectedArrayType(ty.clone()),
                                b.meta,
                            )));
                            (ty.clone(), b.meta)
                        }
                    };
                    if !errors.is_empty() {
                        return Err(errors);
                    }
                    let elem_ty_a = expect_array_type(&ty_a, meta_a)?;
                    let elem_ty_b = expect_array_type(&ty_b, meta_b)?;
                    let tuple_a = expect_tuple_type(&elem_ty_a, meta_a)?;
                    let tuple_b = expect_tuple_type(&elem_ty_b, meta_b)?;
                    if tuple_a.is_empty() || tuple_b.is_empty() || tuple_a[0] != tuple_b[0] {
                        return Err(vec![Some(TypeError(
                            TypeErrorEnum::TypeMismatch(elem_ty_a, elem_ty_b),
                            meta,
                        ))]);
                    }
                    let join_ty = tuple_a[0].clone();
                    let elem_ty = Type::Tuple(vec![elem_ty_a, elem_ty_b]);
                    let mut body_typed = Vec::with_capacity(body.len());
                    env.push();
                    let pattern = pattern.type_check(env, fns, defs, Some(elem_ty))?;
                    for stmt in body {
                        body_typed.push(stmt.type_check(top_level_defs, env, fns, defs)?);
                    }
                    env.pop();
                    Ok(Stmt::new(
                        StmtEnum::JoinLoop(pattern.clone(), join_ty, (a, b), body_typed),
                        meta,
                    ))
                }
                _ => {
                    let binding = binding.type_check(top_level_defs, env, fns, defs)?;
                    let elem_ty = expect_array_type(&binding.ty, meta)?;
                    let mut body_typed = Vec::with_capacity(body.len());
                    env.push();
                    let pattern = pattern.type_check(env, fns, defs, Some(elem_ty))?;
                    for stmt in body {
                        body_typed.push(stmt.type_check(top_level_defs, env, fns, defs)?);
                    }
                    env.pop();
                    Ok(Stmt::new(
                        StmtEnum::ForEachLoop(pattern, binding, body_typed),
                        meta,
                    ))
                }
            },
            ast::StmtEnum::JoinLoop(_, _, _, _) => {
                unreachable!("Untyped expressions should never be join loops")
            }
        }
    }
}

impl UntypedExpr {
    pub(crate) fn type_check(
        &self,
        top_level_defs: &TopLevelTypes,
        env: &mut Env<(Option<Type>, Mutability)>,
        fns: &mut TypedFns,
        defs: &Defs,
    ) -> Result<TypedExpr, TypeErrors> {
        let meta = self.meta;
        let (expr, ty) = match &self.inner {
            ExprEnum::True => (ExprEnum::True, Type::Bool),
            ExprEnum::False => (ExprEnum::False, Type::Bool),
            ExprEnum::NumUnsigned(n, type_suffix) => (
                ExprEnum::NumUnsigned(*n, *type_suffix),
                Type::Unsigned(*type_suffix),
            ),
            ExprEnum::NumSigned(n, type_suffix) => (
                ExprEnum::NumSigned(*n, *type_suffix),
                Type::Signed(*type_suffix),
            ),
            ExprEnum::Identifier(identifier) => match env.get(identifier) {
                Some((Some(ty), _mutability)) => (ExprEnum::Identifier(identifier.clone()), ty),
                Some((None, _mutability)) => {
                    return Err(vec![None]);
                }
                None => match defs.consts.get(identifier.as_str()) {
                    Some(&ty) => (ExprEnum::Identifier(identifier.clone()), ty.clone()),
                    None => {
                        return Err(vec![Some(TypeError(
                            TypeErrorEnum::UnknownIdentifier(identifier.clone()),
                            meta,
                        ))]);
                    }
                },
            },
            ExprEnum::ArrayLiteral(fields) => {
                let mut errors = vec![];
                let array_size = fields.len();

                let mut typed_fields = vec![];
                for field in fields {
                    match field.type_check(top_level_defs, env, fns, defs) {
                        Ok(field) => {
                            typed_fields.push(field);
                        }
                        Err(e) => errors.extend(e),
                    }
                }
                if !errors.is_empty() {
                    return Err(errors);
                }

                let mut elem_ty = typed_fields.first().unwrap().ty.clone();
                if elem_ty == Type::Unsigned(UnsignedNumType::Unspecified) {
                    if let Some(expr) = typed_fields.iter().find(|expr| expr.ty != elem_ty) {
                        elem_ty = expr.ty.clone();
                    }
                }
                if elem_ty == Type::Signed(SignedNumType::Unspecified) {
                    if let Some(expr) = typed_fields.iter().find(|expr| {
                        expr.ty != elem_ty
                            && expr.ty != Type::Unsigned(UnsignedNumType::Unspecified)
                    }) {
                        elem_ty = expr.ty.clone();
                    }
                }

                for field in typed_fields.iter_mut() {
                    check_type(field, &elem_ty)?;
                }
                if errors.is_empty() {
                    let ty = Type::Array(Box::new(elem_ty), array_size);
                    (ExprEnum::ArrayLiteral(typed_fields), ty)
                } else {
                    return Err(errors);
                }
            }
            ExprEnum::ArrayRepeatLiteral(value, size) => {
                let value = value.type_check(top_level_defs, env, fns, defs)?;
                let ty = Type::Array(Box::new(value.ty.clone()), *size);
                (ExprEnum::ArrayRepeatLiteral(Box::new(value), *size), ty)
            }
            ExprEnum::ArrayRepeatLiteralConst(value, size) => match env.get(size) {
                None => match defs.consts.get(size.as_str()) {
                    Some(&ty) if ty == &Type::Unsigned(UnsignedNumType::Usize) => {
                        let value = value.type_check(top_level_defs, env, fns, defs)?;
                        let ty = Type::ArrayConst(Box::new(value.ty.clone()), size.clone());
                        (
                            ExprEnum::ArrayRepeatLiteralConst(Box::new(value), size.clone()),
                            ty,
                        )
                    }
                    Some(&ty) => {
                        let e = TypeErrorEnum::UnexpectedType {
                            expected: Type::Unsigned(UnsignedNumType::Usize),
                            actual: ty.clone(),
                        };
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                    None => {
                        return Err(vec![Some(TypeError(
                            TypeErrorEnum::UnknownIdentifier(size.clone()),
                            meta,
                        ))]);
                    }
                },
                Some(_) => {
                    return Err(vec![Some(TypeError(
                        TypeErrorEnum::ArraySizeNotConst(size.clone()),
                        meta,
                    ))]);
                }
            },
            ExprEnum::ArrayAccess(arr, index) => {
                let arr = arr.type_check(top_level_defs, env, fns, defs)?;
                let mut index = index.type_check(top_level_defs, env, fns, defs)?;
                let elem_ty = expect_array_type(&arr.ty, arr.meta)?;
                check_or_constrain_unsigned(&mut index, UnsignedNumType::Usize)?;
                (
                    ExprEnum::ArrayAccess(Box::new(arr), Box::new(index)),
                    elem_ty,
                )
            }
            ExprEnum::TupleLiteral(values) => {
                let mut errors = vec![];
                let mut typed_values = Vec::with_capacity(values.len());
                let mut types = Vec::with_capacity(values.len());
                for v in values {
                    match v.type_check(top_level_defs, env, fns, defs) {
                        Ok(typed) => {
                            types.push(typed.ty.clone());
                            typed_values.push(typed);
                        }
                        Err(e) => {
                            errors.extend(e);
                        }
                    }
                }
                if errors.is_empty() {
                    let ty = Type::Tuple(types);
                    (ExprEnum::TupleLiteral(typed_values), ty)
                } else {
                    return Err(errors);
                }
            }
            ExprEnum::TupleAccess(tuple, index) => {
                let tuple = tuple.type_check(top_level_defs, env, fns, defs)?;
                let value_types = expect_tuple_type(&tuple.ty, tuple.meta)?;
                if *index < value_types.len() {
                    let ty = value_types[*index].clone();
                    (ExprEnum::TupleAccess(Box::new(tuple), *index), ty)
                } else {
                    let e = TypeErrorEnum::TupleAccessOutOfBounds(value_types.len());
                    return Err(vec![Some(TypeError(e, tuple.meta))]);
                }
            }
            ExprEnum::UnaryOp(UnaryOp::Neg, x) => {
                let x = x.type_check(top_level_defs, env, fns, defs)?;
                let ty = x.ty.clone();
                expect_signed_num_type(&ty, x.meta)?;
                (ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(x)), ty)
            }
            ExprEnum::UnaryOp(UnaryOp::Not, x) => {
                let x = x.type_check(top_level_defs, env, fns, defs)?;
                let ty = x.ty.clone();
                expect_bool_or_num_type(&ty, x.meta)?;
                (ExprEnum::UnaryOp(UnaryOp::Not, Box::new(x)), ty)
            }
            ExprEnum::Op(op, x, y) => match op {
                Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Mod => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let ty = unify(&mut x, &mut y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::ShortCircuitAnd | Op::ShortCircuitOr => {
                    let x = x.type_check(top_level_defs, env, fns, defs)?;
                    let y = y.type_check(top_level_defs, env, fns, defs)?;
                    for (meta, ty) in [(&x.meta, &x.ty), (&y.meta, &y.ty)] {
                        match ty {
                            Type::Bool => {}
                            ty => {
                                return Err(vec![Some(TypeError(
                                    TypeErrorEnum::UnexpectedType {
                                        expected: Type::Bool,
                                        actual: ty.clone(),
                                    },
                                    *meta,
                                ))])
                            }
                        }
                    }
                    (ExprEnum::Op(*op, Box::new(x), Box::new(y)), Type::Bool)
                }
                Op::BitAnd | Op::BitXor | Op::BitOr => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let ty = unify(&mut x, &mut y, meta)?;
                    expect_bool_or_num_type(&ty, meta)?;
                    (ExprEnum::Op(*op, Box::new(x), Box::new(y)), ty)
                }
                Op::GreaterThan | Op::LessThan => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    let ty = unify(&mut x, &mut y, meta)?;
                    expect_num_type(&ty, meta)?;
                    (ExprEnum::Op(*op, Box::new(x), Box::new(y)), Type::Bool)
                }
                Op::Eq | Op::NotEq => {
                    let mut x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    unify(&mut x, &mut y, meta)?;
                    let expr = ExprEnum::Op(*op, Box::new(x), Box::new(y));
                    (expr, Type::Bool)
                }
                Op::ShiftLeft | Op::ShiftRight => {
                    let x = x.type_check(top_level_defs, env, fns, defs)?;
                    let mut y = y.type_check(top_level_defs, env, fns, defs)?;
                    expect_num_type(&x.ty, x.meta)?;
                    check_or_constrain_unsigned(&mut y, UnsignedNumType::U8)?;
                    (ExprEnum::Op(*op, Box::new(x.clone()), Box::new(y)), x.ty)
                }
            },
            ExprEnum::Block(stmts) => {
                env.push();
                let (body, ty) = type_check_block(stmts, top_level_defs, env, fns, defs)?;
                env.pop();
                (ExprEnum::Block(body), ty)
            }
            ExprEnum::FnCall(identifier, args) => {
                let mut errors = vec![];
                if !fns.typed.contains_key(identifier) {
                    if let Some(fn_def) = defs.fns.get(identifier.as_str()) {
                        let fn_def = fn_def.type_check(top_level_defs, fns, defs);
                        fns.typed.insert(identifier.clone(), fn_def.clone());
                        if let Err(e) = fn_def {
                            errors.extend(e);
                        }
                    }
                }
                match (fns.typed.get(identifier), env.get(identifier)) {
                    (Some(Ok(fn_def)), None) => {
                        let ret_ty = fn_def.ty.clone();
                        let mut fn_arg_types = Vec::with_capacity(fn_def.params.len());
                        for param_def in fn_def.params.iter() {
                            fn_arg_types.push(param_def.ty.clone());
                        }
                        let mut arg_types = Vec::with_capacity(args.len());
                        let mut arg_meta = Vec::with_capacity(args.len());
                        let mut arg_exprs = Vec::with_capacity(args.len());
                        for arg in args.iter() {
                            match arg.type_check(top_level_defs, env, fns, defs) {
                                Ok(arg) => {
                                    arg_types.push(arg.ty.clone());
                                    arg_meta.push(arg.meta);
                                    arg_exprs.push(arg);
                                }
                                Err(e) => errors.extend(e),
                            }
                        }
                        if errors.is_empty() {
                            if fn_arg_types.len() != arg_types.len() {
                                let e = TypeErrorEnum::WrongNumberOfArgs {
                                    expected: fn_arg_types.len(),
                                    actual: arg_types.len(),
                                };
                                errors.push(Some(TypeError(e, meta)));
                            }
                            for (expected, actual) in fn_arg_types.into_iter().zip(&mut arg_exprs) {
                                if let Err(e) = check_type(actual, &expected) {
                                    errors.extend(e);
                                }
                            }
                        }
                        if errors.is_empty() {
                            let expr = ExprEnum::FnCall(identifier.clone(), arg_exprs);
                            (expr, ret_ty)
                        } else {
                            return Err(errors);
                        }
                    }
                    (Some(Err(_)), None) => {
                        // error was added during typechecking of fn, so we only push a None error
                        // to mark the fn call as failed (the final output will display the root
                        // cause error instead)
                        errors.push(None);
                        return Err(errors);
                    }
                    (None, _) => {
                        let e = TypeErrorEnum::UnknownIdentifier(identifier.clone());
                        errors.push(Some(TypeError(e, meta)));
                        return Err(errors);
                    }
                    (_, Some(_)) => {
                        let e = TypeErrorEnum::NoTopLevelFn(identifier.clone());
                        errors.push(Some(TypeError(e, meta)));
                        return Err(errors);
                    }
                }
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.type_check(top_level_defs, env, fns, defs);
                let case_true = case_true.type_check(top_level_defs, env, fns, defs);
                let case_false = case_false.type_check(top_level_defs, env, fns, defs);
                match (condition, case_true, case_false) {
                    (Ok(mut condition), Ok(mut case_true), Ok(mut case_false)) => {
                        check_type(&mut condition, &Type::Bool)?;
                        let ty = unify(&mut case_true, &mut case_false, meta)?;
                        let expr = ExprEnum::If(
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
                let ty = ty.as_concrete_type(top_level_defs)?;
                let expr = expr.type_check(top_level_defs, env, fns, defs)?;
                expect_bool_or_num_type(&expr.ty, meta)?;
                expect_bool_or_num_type(&ty, meta)?;
                (ExprEnum::Cast(ty.clone(), Box::new(expr)), ty)
            }
            ExprEnum::Range(from, to, num_ty) => {
                if from >= to || (to - from) > u32::MAX as u64 {
                    let e = TypeErrorEnum::InvalidRange(*from, *to);
                    return Err(vec![Some(TypeError(e, meta))]);
                }
                let ty = Type::Array(Box::new(Type::Unsigned(*num_ty)), (to - from) as usize);
                (ExprEnum::Range(*from, *to, *num_ty), ty)
            }
            ExprEnum::EnumLiteral(identifier, variant_name, variant) => {
                if let Some(enum_def) = defs.enums.get(identifier.as_str()) {
                    if let Some(types) = enum_def.get(variant_name.as_str()) {
                        match (variant, types) {
                            (VariantExprEnum::Unit, None) => (
                                ExprEnum::EnumLiteral(
                                    identifier.clone(),
                                    variant_name.clone(),
                                    VariantExprEnum::Unit,
                                ),
                                Type::Enum(identifier.clone()),
                            ),
                            (VariantExprEnum::Tuple(values), Some(types)) => {
                                if values.len() != types.len() {
                                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                                        expected: types.len(),
                                        actual: values.len(),
                                    };
                                    return Err(vec![Some(TypeError(e, meta))]);
                                }
                                let mut errors = vec![];
                                let mut exprs = Vec::with_capacity(values.len());
                                for (v, ty) in values.iter().zip(types) {
                                    match v.type_check(top_level_defs, env, fns, defs) {
                                        Ok(mut expr) => {
                                            if let Err(e) = check_type(&mut expr, ty) {
                                                errors.extend(e);
                                            }
                                            exprs.push(expr);
                                        }
                                        Err(e) => errors.extend(e),
                                    }
                                }
                                if errors.is_empty() {
                                    (
                                        ExprEnum::EnumLiteral(
                                            identifier.clone(),
                                            variant_name.clone(),
                                            VariantExprEnum::Tuple(exprs),
                                        ),
                                        Type::Enum(identifier.clone()),
                                    )
                                } else {
                                    return Err(errors);
                                }
                            }
                            (VariantExprEnum::Unit, Some(_)) => {
                                let e = TypeErrorEnum::ExpectedTupleVariantFoundUnitVariant;
                                return Err(vec![Some(TypeError(e, meta))]);
                            }
                            (VariantExprEnum::Tuple(_), None) => {
                                let e = TypeErrorEnum::ExpectedUnitVariantFoundTupleVariant;
                                return Err(vec![Some(TypeError(e, meta))]);
                            }
                        }
                    } else {
                        let e = TypeErrorEnum::UnknownEnumVariant(
                            identifier.clone(),
                            variant_name.to_string(),
                        );
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                } else {
                    let e =
                        TypeErrorEnum::UnknownEnum(identifier.clone(), variant_name.to_string());
                    return Err(vec![Some(TypeError(e, meta))]);
                }
            }
            ExprEnum::Match(expr, clauses) => {
                let expr = expr.type_check(top_level_defs, env, fns, defs)?;
                let ty = &expr.ty;

                match ty {
                    Type::Bool
                    | Type::Unsigned(_)
                    | Type::Signed(_)
                    | Type::Tuple(_)
                    | Type::Struct(_)
                    | Type::Enum(_) => {}
                    Type::Fn(_, _) | Type::Array(_, _) | Type::ArrayConst(_, _) => {
                        let e = TypeErrorEnum::TypeDoesNotSupportPatternMatching(ty.clone());
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                    Type::UntypedTopLevelDefinition(_, _) => unreachable!(
                        "Untyped top level types should have been typechecked at this point"
                    ),
                }

                let mut errors = vec![];
                let mut typed_clauses = Vec::with_capacity(clauses.len());

                for (pattern, expr) in clauses {
                    env.push();
                    let pattern = pattern.type_check(env, fns, defs, Some(ty.clone()));
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
                if !errors.is_empty() {
                    return Err(errors);
                }

                let ret_ty = {
                    let mut ret_ty = typed_clauses
                        .first()
                        .map(|(_, expr)| expr.ty.clone())
                        .unwrap();
                    if ret_ty == Type::Unsigned(UnsignedNumType::Unspecified) {
                        if let Some((_, expr)) =
                            typed_clauses.iter().find(|(_, expr)| expr.ty != ret_ty)
                        {
                            ret_ty = expr.ty.clone();
                        }
                    }
                    if ret_ty == Type::Signed(SignedNumType::Unspecified) {
                        if let Some((_, expr)) = typed_clauses.iter().find(|(_, expr)| {
                            expr.ty != ret_ty
                                && expr.ty != Type::Unsigned(UnsignedNumType::Unspecified)
                        }) {
                            ret_ty = expr.ty.clone();
                        }
                    }

                    for (_, expr) in typed_clauses.iter_mut() {
                        if ret_ty != expr.ty {
                            if let Type::Unsigned(expected) = ret_ty {
                                check_or_constrain_unsigned(expr, expected)?;
                            } else if let Type::Signed(expected) = ret_ty {
                                check_or_constrain_signed(expr, expected)?;
                            } else {
                                let e = TypeErrorEnum::UnexpectedType {
                                    expected: ret_ty.clone(),
                                    actual: expr.ty.clone(),
                                };
                                errors.push(Some(TypeError(e, expr.meta)));
                            }
                        }
                    }
                    ret_ty.clone()
                };

                let patterns: Vec<_> = typed_clauses.iter().map(|(p, _)| p).collect();
                if let Err(e) = check_exhaustiveness(patterns.as_slice(), ty, defs, meta) {
                    errors.push(Some(e));
                }

                if errors.is_empty() {
                    (ExprEnum::Match(Box::new(expr), typed_clauses), ret_ty)
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
                                    if let Err(e) = check_type(&mut typed_field, expected_type) {
                                        errors.extend(e);
                                    }
                                    typed_fields.push((field_name.clone(), typed_field));
                                }
                                Err(e) => errors.extend(e),
                            }
                        } else {
                            let e =
                                TypeErrorEnum::UnknownStructField(name.clone(), field_name.clone());
                            errors.push(Some(TypeError(e, meta)));
                        }
                    }
                    if struct_def.len() > fields.len() {
                        for expected_field_name in struct_def.keys() {
                            if !fields.iter().any(|(f, _)| f == expected_field_name) {
                                let e = TypeErrorEnum::MissingStructField(
                                    name.clone(),
                                    expected_field_name.to_string(),
                                );
                                errors.push(Some(TypeError(e, meta)));
                            }
                        }
                    }
                    if errors.is_empty() {
                        (
                            ExprEnum::StructLiteral(name.clone(), typed_fields),
                            Type::Struct(name.clone()),
                        )
                    } else {
                        return Err(errors);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownStruct(name.clone());
                    return Err(vec![Some(TypeError(e, meta))]);
                }
            }
            ExprEnum::StructAccess(struct_expr, field) => {
                let struct_expr = struct_expr.type_check(top_level_defs, env, fns, defs)?;
                let name = expect_struct_type(&struct_expr.ty, struct_expr.meta)?;
                if let Some((_, struct_def)) = defs.structs.get(name.as_str()) {
                    if let Some(field_ty) = struct_def.get(field.as_str()) {
                        (
                            ExprEnum::StructAccess(Box::new(struct_expr), field.clone()),
                            field_ty.clone(),
                        )
                    } else {
                        let e = TypeErrorEnum::UnknownStructField(name.clone(), field.clone());
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownStruct(name.clone());
                    return Err(vec![Some(TypeError(e, meta))]);
                }
            }
        };
        Ok(Expr::typed(expr, ty, meta))
    }
}

impl UntypedPattern {
    fn type_check(
        &self,
        env: &mut Env<(Option<Type>, Mutability)>,
        _fns: &mut TypedFns,
        defs: &Defs,
        ty: Option<Type>,
    ) -> Result<TypedPattern, TypeErrors> {
        let Pattern(pattern, meta, _) = self;
        let meta = *meta;
        let pattern = match pattern {
            PatternEnum::Identifier(s) => {
                env.let_in_current_scope(s.clone(), (ty.clone(), Mutability::Immutable));
                PatternEnum::Identifier(s.clone())
            }
            PatternEnum::True => match &ty {
                Some(Type::Bool) => PatternEnum::True,
                Some(ty) => {
                    let e = TypeErrorEnum::UnexpectedType {
                        expected: Type::Bool,
                        actual: ty.clone(),
                    };
                    return Err(vec![Some(TypeError(e, meta))]);
                }
                None => {
                    return Err(vec![None]);
                }
            },
            PatternEnum::False => match &ty {
                Some(Type::Bool) => PatternEnum::False,
                Some(ty) => {
                    let e = TypeErrorEnum::UnexpectedType {
                        expected: Type::Bool,
                        actual: ty.clone(),
                    };
                    return Err(vec![Some(TypeError(e, meta))]);
                }
                None => {
                    return Err(vec![None]);
                }
            },
            PatternEnum::NumUnsigned(n, suffix) => {
                if let Some(ty) = &ty {
                    expect_num_type(ty, meta)?;
                    PatternEnum::NumUnsigned(*n, *suffix)
                } else {
                    return Err(vec![None]);
                }
            }
            PatternEnum::NumSigned(n, suffix) => {
                if let Some(ty) = &ty {
                    expect_signed_num_type(ty, meta)?;
                    PatternEnum::NumSigned(*n, *suffix)
                } else {
                    return Err(vec![None]);
                }
            }
            PatternEnum::UnsignedInclusiveRange(from, to, suffix) => {
                if let Some(ty) = &ty {
                    expect_num_type(ty, meta)?;
                    PatternEnum::UnsignedInclusiveRange(*from, *to, *suffix)
                } else {
                    return Err(vec![None]);
                }
            }
            PatternEnum::SignedInclusiveRange(from, to, suffix) => {
                if let Some(ty) = &ty {
                    expect_signed_num_type(ty, meta)?;
                    PatternEnum::SignedInclusiveRange(*from, *to, *suffix)
                } else {
                    return Err(vec![None]);
                }
            }
            PatternEnum::Tuple(fields) => {
                if let Some(ty) = &ty {
                    let field_types = expect_tuple_type(ty, meta)?;
                    if field_types.len() != fields.len() {
                        let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                            expected: field_types.len(),
                            actual: fields.len(),
                        };
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                    let mut errors = vec![];
                    let mut typed_fields = Vec::with_capacity(fields.len());
                    for (field, ty) in fields.iter().zip(field_types) {
                        match field.type_check(env, _fns, defs, Some(ty)) {
                            Ok(typed_field) => typed_fields.push(typed_field),
                            Err(e) => errors.extend(e),
                        }
                    }
                    if errors.is_empty() {
                        PatternEnum::Tuple(typed_fields)
                    } else {
                        return Err(errors);
                    }
                } else {
                    let mut errors = vec![None];
                    for field in fields.iter() {
                        match field.type_check(env, _fns, defs, ty.clone()) {
                            Ok(_) => {}
                            Err(e) => errors.extend(e),
                        }
                    }
                    return Err(errors);
                }
            }
            PatternEnum::Struct(struct_name, fields)
            | PatternEnum::StructIgnoreRemaining(struct_name, fields) => {
                let ignore_remaining_fields =
                    matches!(pattern, PatternEnum::StructIgnoreRemaining(_, _));
                if let Some(ty) = &ty {
                    let struct_def_name = expect_struct_type(ty, meta)?;
                    if &struct_def_name != struct_name {
                        let e = TypeErrorEnum::UnexpectedType {
                            expected: ty.clone(),
                            actual: Type::Struct(struct_name.clone()),
                        };
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                }
                if let Some((_, struct_def)) = defs.structs.get(struct_name.as_str()) {
                    let mut errors = vec![];
                    let mut typed_fields = Vec::with_capacity(fields.len());
                    for (field_name, field_value) in fields {
                        if let Some(field_type) = struct_def.get(field_name.as_str()) {
                            match field_value.type_check(env, _fns, defs, Some(field_type.clone()))
                            {
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
                            errors.push(Some(TypeError(e, meta)));
                        }
                    }
                    if !ignore_remaining_fields && struct_def.len() > fields.len() {
                        for expected_field_name in struct_def.keys() {
                            if !fields.iter().any(|(f, _)| f == expected_field_name) {
                                let e = TypeErrorEnum::MissingStructField(
                                    struct_name.clone(),
                                    expected_field_name.to_string(),
                                );
                                errors.push(Some(TypeError(e, meta)));
                            }
                        }
                    }
                    if errors.is_empty() {
                        PatternEnum::Struct(struct_name.clone(), typed_fields)
                    } else {
                        return Err(errors);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownStruct(struct_name.clone());
                    return Err(vec![Some(TypeError(e, meta))]);
                }
            }
            PatternEnum::EnumUnit(enum_name, variant_name)
            | PatternEnum::EnumTuple(enum_name, variant_name, _) => {
                if let Some(ty) = &ty {
                    match &ty {
                        Type::Enum(enum_def_name) if enum_def_name == enum_name => {}
                        _ => {
                            let e = TypeErrorEnum::UnexpectedType {
                                expected: Type::Enum(enum_name.clone()),
                                actual: ty.clone(),
                            };
                            return Err(vec![Some(TypeError(e, meta))]);
                        }
                    }
                }
                if let Some(enum_def) = defs.enums.get(enum_name.as_str()) {
                    if let Some(variant) = enum_def.get(variant_name.as_str()) {
                        match (pattern, variant) {
                            (PatternEnum::EnumUnit(_, _), None) => {
                                PatternEnum::EnumUnit(enum_name.clone(), variant_name.clone())
                            }
                            (PatternEnum::EnumTuple(_, _, fields), Some(field_types)) => {
                                if field_types.len() != fields.len() {
                                    let e = TypeErrorEnum::UnexpectedEnumVariantArity {
                                        expected: field_types.len(),
                                        actual: fields.len(),
                                    };
                                    return Err(vec![Some(TypeError(e, meta))]);
                                }
                                let mut errors = vec![];
                                let mut typed_fields = Vec::with_capacity(fields.len());
                                for (field, ty) in fields.iter().zip(field_types) {
                                    match field.type_check(env, _fns, defs, Some(ty.clone())) {
                                        Ok(typed_field) => typed_fields.push(typed_field),
                                        Err(e) => errors.extend(e),
                                    }
                                }
                                if errors.is_empty() {
                                    PatternEnum::EnumTuple(
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
                                return Err(vec![Some(TypeError(e, meta))]);
                            }
                            (PatternEnum::EnumTuple(_, _, _), None) => {
                                let e = TypeErrorEnum::ExpectedUnitVariantFoundTupleVariant;
                                return Err(vec![Some(TypeError(e, meta))]);
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        let e = TypeErrorEnum::UnknownEnumVariant(
                            enum_name.clone(),
                            variant_name.to_string(),
                        );
                        return Err(vec![Some(TypeError(e, meta))]);
                    }
                } else {
                    let e = TypeErrorEnum::UnknownEnum(enum_name.clone(), variant_name.to_string());
                    return Err(vec![Some(TypeError(e, meta))]);
                }
            }
        };
        if let Some(ty) = ty {
            Ok(Pattern::typed(pattern, ty, meta))
        } else {
            Err(vec![None])
        }
    }
}

// Implements the algorithm described at
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/thir/pattern/usefulness/index.html
// (which implements the paper http://moscova.inria.fr/~maranget/papers/warn/index.html)
fn check_exhaustiveness(
    patterns: &[&TypedPattern],
    ty: &Type,
    defs: &Defs,
    meta: MetaInfo,
) -> Result<(), TypeError> {
    let patterns: Vec<Vec<TypedPattern>> = patterns.iter().map(|&p| vec![p.clone()]).collect();
    let wildcard_pattern = vec![Pattern::typed(
        PatternEnum::Identifier("_".to_string()),
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
    UnsignedInclusiveRange(UnsignedNumType, u64, u64),
    SignedInclusiveRange(SignedNumType, i64, i64),
    Tuple(Vec<Type>),
    Struct(String, Vec<(String, Type)>),
    Variant(String, String, Option<Vec<Type>>),
    Array(Box<Type>, usize),
    ArrayConst(Box<Type>, String),
}

type PatternStack = Vec<TypedPattern>;

fn specialize(ctor: &Ctor, pattern: &[TypedPattern]) -> Vec<PatternStack> {
    let head = if let Some(head) = pattern.first() {
        head
    } else {
        return vec![];
    };
    let tail = pattern.iter().skip(1).cloned();
    let Pattern(head_enum, meta, _) = head;
    match ctor {
        Ctor::True => match head_enum {
            PatternEnum::Identifier(_) | PatternEnum::True => {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::False => match head_enum {
            PatternEnum::Identifier(_) | PatternEnum::False => {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::UnsignedInclusiveRange(_, min, max) => match head_enum {
            PatternEnum::Identifier(_) => vec![tail.collect()],
            PatternEnum::NumUnsigned(n, _) if n == min && n == max => vec![tail.collect()],
            PatternEnum::UnsignedInclusiveRange(n_min, n_max, _)
                if n_min <= min && max <= n_max =>
            {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::SignedInclusiveRange(_, min, max) => match head_enum {
            PatternEnum::Identifier(_) => vec![tail.collect()],
            PatternEnum::NumUnsigned(n, _)
                if *min >= 0 && *max >= 0 && *n == *min as u64 && *n == *max as u64 =>
            {
                vec![tail.collect()]
            }
            PatternEnum::NumSigned(n, _) if n == min && n == max => vec![tail.collect()],
            PatternEnum::UnsignedInclusiveRange(n_min, n_max, _)
                if *min >= 0 && *max >= 0 && *n_min <= *min as u64 && *max as u64 <= *n_max =>
            {
                vec![tail.collect()]
            }
            PatternEnum::SignedInclusiveRange(n_min, n_max, _) if n_min <= min && max <= n_max => {
                vec![tail.collect()]
            }
            _ => vec![],
        },
        Ctor::Tuple(field_types) => match head_enum {
            PatternEnum::Identifier(_) => {
                let mut fields = Vec::with_capacity(field_types.len());
                for ty in field_types {
                    let wildcard = PatternEnum::Identifier("_".to_string());
                    let p = Pattern::typed(wildcard, ty.clone(), *meta);
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            PatternEnum::Tuple(fields) => {
                vec![fields.iter().cloned().chain(tail).collect()]
            }
            _ => vec![],
        },
        Ctor::Array(_, _) | Ctor::ArrayConst(_, _) => match head_enum {
            PatternEnum::Identifier(_) => vec![tail.collect()],
            _ => vec![],
        },
        Ctor::Struct(struct_name, field_types) => match head_enum {
            PatternEnum::Identifier(_) => {
                let mut fields = Vec::with_capacity(field_types.len());
                for (_, ty) in field_types {
                    let wildcard = PatternEnum::Identifier("_".to_string());
                    let p = Pattern::typed(wildcard, ty.clone(), *meta);
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            PatternEnum::Struct(struct_name_in_pattern, fields)
            | PatternEnum::StructIgnoreRemaining(struct_name_in_pattern, fields)
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
            PatternEnum::Identifier(_) => {
                let field_types = fields.as_deref().unwrap_or_default();
                let mut fields = Vec::with_capacity(field_types.len());
                for ty in field_types {
                    let wildcard = PatternEnum::Identifier("_".to_string());
                    let p = Pattern::typed(wildcard, ty.clone(), *meta);
                    fields.push(p);
                }
                vec![fields.into_iter().chain(tail).collect()]
            }
            PatternEnum::EnumUnit(_, v2) if v1 == v2 => vec![tail.collect()],
            PatternEnum::EnumTuple(_, v2, fields) if v1 == v2 => {
                vec![fields.iter().cloned().chain(tail).collect()]
            }
            _ => vec![],
        },
    }
}

fn split_unsigned_range(
    ty: UnsignedNumType,
    patterns: &[PatternStack],
    min: u64,
    max: u64,
) -> Vec<Ctor> {
    let mut split_points = vec![min as u128, max as u128 + 1];
    for p in patterns {
        let head = p.first().unwrap();
        let Pattern(head_enum, _, _) = head;
        match head_enum {
            PatternEnum::NumUnsigned(n, _) => split_points.push(*n as u128),
            PatternEnum::NumSigned(n, _) if *n >= 0 => split_points.push(*n as u128),
            PatternEnum::UnsignedInclusiveRange(min, max, _) => {
                split_points.push(*min as u128);
                split_points.push(*max as u128 + 1);
            }
            PatternEnum::SignedInclusiveRange(min, max, _) => {
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
            ranges.push(Ctor::UnsignedInclusiveRange(
                ty,
                range[0] as u64,
                range[0] as u64,
            ));
        }
        if range[0] >= min as u128 && range[1] - 1 <= max as u128 {
            if range[0] < range[1] - 1 {
                ranges.push(Ctor::UnsignedInclusiveRange(
                    ty,
                    range[0] as u64 + 1,
                    range[1] as u64 - 1,
                ));
            } else {
                ranges.push(Ctor::UnsignedInclusiveRange(
                    ty,
                    range[0] as u64,
                    range[1] as u64 - 1,
                ));
            }
        }
    }
    ranges
}

fn split_signed_range(
    ty: SignedNumType,
    patterns: &[PatternStack],
    min: i64,
    max: i64,
) -> Vec<Ctor> {
    let mut split_points = vec![min as i128, max as i128 + 1];
    for p in patterns {
        let head = p.first().unwrap();
        let Pattern(head_enum, _, _) = head;
        match head_enum {
            PatternEnum::NumUnsigned(n, _) => split_points.push(*n as i128),
            PatternEnum::NumSigned(n, _) if *n >= 0 => split_points.push(*n as i128),
            PatternEnum::UnsignedInclusiveRange(min, max, _) => {
                split_points.push(*min as i128);
                split_points.push(*max as i128 + 1);
            }
            PatternEnum::SignedInclusiveRange(min, max, _) => {
                if *min >= 0 {
                    split_points.push(*min as i128);
                }
                if *max >= 0 {
                    split_points.push(*max as i128 + 1);
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
            ranges.push(Ctor::SignedInclusiveRange(
                ty,
                range[0] as i64,
                range[0] as i64,
            ));
        }
        if range[0] >= min as i128 && range[1] - 1 <= max as i128 {
            ranges.push(Ctor::SignedInclusiveRange(
                ty,
                range[0] as i64,
                range[1] as i64 - 1,
            ));
        }
    }
    ranges
}

fn split_ctor(patterns: &[PatternStack], q: &[TypedPattern], defs: &Defs) -> Vec<Ctor> {
    let head = q.first().unwrap();
    let Pattern(head_enum, _, ty) = head;
    match ty {
        Type::Bool => vec![Ctor::True, Ctor::False],
        Type::Unsigned(ty) => match head_enum {
            PatternEnum::Identifier(_) => {
                split_unsigned_range(*ty, patterns, 0, ty.max().unwrap_or(u32::MAX as u64))
            }
            PatternEnum::NumUnsigned(n, _) => {
                vec![Ctor::UnsignedInclusiveRange(*ty, *n, *n)]
            }
            PatternEnum::UnsignedInclusiveRange(min, max, _) => {
                split_unsigned_range(*ty, patterns, *min, *max)
            }
            _ => panic!("cannot split {head_enum:?} for type {ty:?}"),
        },
        Type::Signed(ty) => match head_enum {
            PatternEnum::Identifier(_) => {
                vec![Ctor::SignedInclusiveRange(
                    *ty,
                    ty.min().unwrap_or(i32::MIN as i64),
                    ty.max().unwrap_or(i32::MAX as i64),
                )]
            }
            PatternEnum::NumUnsigned(n, _) => {
                vec![Ctor::SignedInclusiveRange(*ty, *n as i64, *n as i64)]
            }
            PatternEnum::NumSigned(n, _) => vec![Ctor::SignedInclusiveRange(*ty, *n, *n)],
            PatternEnum::UnsignedInclusiveRange(min, max, _) => {
                split_signed_range(*ty, patterns, *min as i64, *max as i64)
            }
            PatternEnum::SignedInclusiveRange(min, max, _) => {
                split_signed_range(*ty, patterns, *min, *max)
            }
            _ => panic!("cannot split {head_enum:?} for type {ty:?}"),
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
        Type::ArrayConst(elem_ty, size) => vec![Ctor::ArrayConst(elem_ty.clone(), size.clone())],
        Type::Fn(_, _) => {
            panic!("Type {ty:?} does not support pattern matching")
        }
        Type::UntypedTopLevelDefinition(_, _) => {
            unreachable!("Untyped top level types should have been typechecked at this point")
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
                        Ctor::True => {
                            witness.insert(0, Pattern::typed(PatternEnum::True, Type::Bool, meta))
                        }
                        Ctor::False => {
                            witness.insert(0, Pattern::typed(PatternEnum::False, Type::Bool, meta))
                        }
                        Ctor::UnsignedInclusiveRange(ty, min, max) => witness.insert(
                            0,
                            Pattern::typed(
                                PatternEnum::UnsignedInclusiveRange(*min, *max, *ty),
                                Type::Unsigned(*ty),
                                meta,
                            ),
                        ),
                        Ctor::SignedInclusiveRange(ty, min, max) => witness.insert(
                            0,
                            Pattern::typed(
                                PatternEnum::SignedInclusiveRange(*min, *max, *ty),
                                Type::Signed(*ty),
                                meta,
                            ),
                        ),
                        Ctor::Tuple(fields) => {
                            witness = vec![Pattern::typed(
                                PatternEnum::Tuple(witness),
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
                            witness = vec![Pattern::typed(
                                PatternEnum::Struct(struct_name.clone(), witness_fields),
                                Type::Struct(struct_name.clone()),
                                meta,
                            )]
                        }
                        Ctor::Variant(enum_name, variant_name, None) => {
                            witness = vec![Pattern::typed(
                                PatternEnum::EnumUnit(enum_name.clone(), variant_name.clone()),
                                Type::Enum(enum_name.clone()),
                                meta,
                            )]
                        }
                        Ctor::Variant(enum_name, variant_name, Some(_)) => {
                            witness = vec![Pattern::typed(
                                PatternEnum::EnumTuple(
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
                            Pattern::typed(
                                PatternEnum::Identifier("_".to_string()),
                                Type::Array(elem_ty.clone(), *size),
                                meta,
                            ),
                        ),
                        Ctor::ArrayConst(elem_ty, size) => witness.insert(
                            0,
                            Pattern::typed(
                                PatternEnum::Identifier("_".to_string()),
                                Type::ArrayConst(elem_ty.clone(), size.clone()),
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

fn expect_array_type(ty: &Type, meta: MetaInfo) -> Result<Type, TypeErrors> {
    match ty {
        Type::Array(elem, _) | Type::ArrayConst(elem, _) => Ok(*elem.clone()),
        _ => Err(vec![Some(TypeError(
            TypeErrorEnum::ExpectedArrayType(ty.clone()),
            meta,
        ))]),
    }
}

fn expect_struct_type(ty: &Type, meta: MetaInfo) -> Result<String, TypeErrors> {
    match ty {
        Type::Struct(name) => Ok(name.clone()),
        _ => Err(vec![Some(TypeError(
            TypeErrorEnum::ExpectedStructType(ty.clone()),
            meta,
        ))]),
    }
}

fn expect_tuple_type(ty: &Type, meta: MetaInfo) -> Result<Vec<Type>, TypeErrors> {
    match ty {
        Type::Tuple(types) => Ok(types.clone()),
        _ => Err(vec![Some(TypeError(
            TypeErrorEnum::ExpectedTupleType(ty.clone()),
            meta,
        ))]),
    }
}

fn expect_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeErrors> {
    match ty {
        Type::Unsigned(_) | Type::Signed(_) => Ok(()),
        _ => Err(vec![Some(TypeError(
            TypeErrorEnum::ExpectedNumberType(ty.clone()),
            meta,
        ))]),
    }
}

fn expect_signed_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeErrors> {
    match ty {
        Type::Signed(_) => Ok(()),
        _ => Err(vec![Some(TypeError(
            TypeErrorEnum::ExpectedSignedNumberType(ty.clone()),
            meta,
        ))]),
    }
}

fn expect_bool_or_num_type(ty: &Type, meta: MetaInfo) -> Result<(), TypeErrors> {
    if let Type::Bool = ty {
        return Ok(());
    };
    if let Ok(()) = expect_num_type(ty, meta) {
        return Ok(());
    }
    Err(vec![Some(TypeError(
        TypeErrorEnum::ExpectedBoolOrNumberType(ty.clone()),
        meta,
    ))])
}

pub(crate) fn check_or_constrain_unsigned(
    expr: &mut TypedExpr,
    expected: UnsignedNumType,
) -> Result<(), TypeErrors> {
    if expr.ty != Type::Unsigned(expected)
        && expr.ty != Type::Unsigned(UnsignedNumType::Unspecified)
    {
        let e = TypeErrorEnum::UnexpectedType {
            expected: Type::Unsigned(expected),
            actual: expr.ty.clone(),
        };
        return Err(vec![Some(TypeError(e, expr.meta))]);
    }
    if let Some(max) = UnsignedNumType::max(&expected) {
        if let ExprEnum::NumUnsigned(n, _) = expr.inner {
            if n > max {
                let e = TypeErrorEnum::UnexpectedType {
                    expected: Type::Unsigned(expected),
                    actual: expr.ty.clone(),
                };
                return Err(vec![Some(TypeError(e, expr.meta))]);
            }
        }
    }
    expr.ty = Type::Unsigned(expected);
    Ok(())
}

pub(crate) fn check_or_constrain_signed(
    expr: &mut TypedExpr,
    expected: SignedNumType,
) -> Result<(), TypeErrors> {
    if expr.ty != Type::Signed(expected)
        && expr.ty != Type::Signed(SignedNumType::Unspecified)
        && expr.ty != Type::Unsigned(UnsignedNumType::Unspecified)
    {
        let e = TypeErrorEnum::UnexpectedType {
            expected: Type::Signed(expected),
            actual: expr.ty.clone(),
        };
        return Err(vec![Some(TypeError(e, expr.meta))]);
    }
    if let Some(min) = SignedNumType::min(&expected) {
        if let ExprEnum::NumSigned(n, _) = expr.inner {
            if n < min {
                let e = TypeErrorEnum::UnexpectedType {
                    expected: Type::Signed(expected),
                    actual: expr.ty.clone(),
                };
                return Err(vec![Some(TypeError(e, expr.meta))]);
            }
        }
    }
    if let Some(max) = SignedNumType::max(&expected) {
        if let ExprEnum::NumUnsigned(n, _) = expr.inner {
            if n > max as u64 {
                let e = TypeErrorEnum::UnexpectedType {
                    expected: Type::Signed(expected),
                    actual: expr.ty.clone(),
                };
                return Err(vec![Some(TypeError(e, expr.meta))]);
            }
        } else if let ExprEnum::NumSigned(n, _) = expr.inner {
            if n > max {
                let e = TypeErrorEnum::UnexpectedType {
                    expected: Type::Signed(expected),
                    actual: expr.ty.clone(),
                };
                return Err(vec![Some(TypeError(e, expr.meta))]);
            }
        }
    }
    expr.ty = Type::Signed(expected);
    Ok(())
}

pub(crate) fn constrain_type(expr: &mut TypedExpr, expected: &Type) -> Result<(), TypeErrors> {
    fn overwrite_ty_if_necessary(actual: &mut Type, expected: &Type) {
        match expected {
            Type::Unsigned(_) => {
                if actual == &Type::Unsigned(UnsignedNumType::Unspecified) {
                    *actual = expected.clone();
                }
            }
            Type::Signed(_) => {
                if actual == &Type::Unsigned(UnsignedNumType::Unspecified)
                    || actual == &Type::Signed(SignedNumType::Unspecified)
                {
                    *actual = expected.clone();
                }
            }
            _ => {}
        }
    }
    match (&mut expr.inner, expected) {
        (ExprEnum::ArrayLiteral(elems), Type::Array(elem_ty, _) | Type::ArrayConst(elem_ty, _)) => {
            for elem in elems {
                constrain_type(elem, elem_ty)?;
            }
            if let Type::Array(actual, _) | Type::ArrayConst(actual, _) = &mut expr.ty {
                overwrite_ty_if_necessary(actual, elem_ty);
            }
        }
        (
            ExprEnum::ArrayRepeatLiteral(elem, _) | ExprEnum::ArrayRepeatLiteralConst(elem, _),
            Type::Array(elem_ty, _) | Type::ArrayConst(elem_ty, _),
        ) => {
            constrain_type(elem, elem_ty)?;
            if let Type::Array(actual, _) | Type::ArrayConst(actual, _) = &mut expr.ty {
                overwrite_ty_if_necessary(actual, elem_ty);
            }
        }
        (ExprEnum::TupleLiteral(elems), Type::Tuple(elem_tys)) if elems.len() == elem_tys.len() => {
            for (elem, elem_ty) in elems.iter_mut().zip(elem_tys) {
                constrain_type(elem, elem_ty)?;
            }
            if let Type::Tuple(actual_elem_tys) = &mut expr.ty {
                for (actual, expected) in actual_elem_tys.iter_mut().zip(elem_tys) {
                    overwrite_ty_if_necessary(actual, expected);
                }
            }
        }
        (ExprEnum::Identifier(_), Type::Array(elem_ty, _) | Type::ArrayConst(elem_ty, _)) => {
            if let Type::Array(actual, _) | Type::ArrayConst(actual, _) = &mut expr.ty {
                overwrite_ty_if_necessary(actual, elem_ty);
            }
        }
        (ExprEnum::Identifier(_), Type::Tuple(elem_tys)) => {
            if let Type::Tuple(actual_elem_tys) = &mut expr.ty {
                for (actual, expected) in actual_elem_tys.iter_mut().zip(elem_tys) {
                    overwrite_ty_if_necessary(actual, expected);
                }
            }
        }
        (ExprEnum::Match(_, clauses), ty) => {
            for (_, body) in clauses {
                constrain_type(body, ty)?;
            }
        }
        (ExprEnum::UnaryOp(op, expr), ty) => match op {
            UnaryOp::Not | UnaryOp::Neg => constrain_type(expr, ty)?,
        },
        (ExprEnum::Op(op, a, b), ty) => match op {
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Mod
            | Op::BitAnd
            | Op::BitXor
            | Op::BitOr => {
                constrain_type(a, ty)?;
                constrain_type(b, ty)?;
            }
            Op::ShiftLeft | Op::ShiftRight => constrain_type(a, ty)?,
            Op::GreaterThan
            | Op::LessThan
            | Op::Eq
            | Op::NotEq
            | Op::ShortCircuitAnd
            | Op::ShortCircuitOr => {}
        },
        (ExprEnum::Block(stmts), ty) => {
            if let Some(last) = stmts.last_mut() {
                if let StmtEnum::Expr(expr) = &mut last.inner {
                    constrain_type(expr, ty)?;
                }
            }
        }
        (ExprEnum::If(_, then_expr, else_expr), ty) => {
            constrain_type(then_expr, ty)?;
            constrain_type(else_expr, ty)?;
        }
        (_, Type::Unsigned(ty)) => check_or_constrain_unsigned(expr, *ty)?,
        (_, Type::Signed(ty)) => check_or_constrain_signed(expr, *ty)?,
        _ => {}
    }
    overwrite_ty_if_necessary(&mut expr.ty, expected);
    Ok(())
}

pub(crate) fn check_type(expr: &mut TypedExpr, expected: &Type) -> Result<(), TypeErrors> {
    constrain_type(expr, expected)?;
    if &expr.ty == expected {
        Ok(())
    } else {
        let expected = expected.clone();
        let e = TypeErrorEnum::UnexpectedType {
            expected,
            actual: expr.ty.clone(),
        };
        Err(vec![Some(TypeError(e, expr.meta))])
    }
}

fn unify(e1: &mut TypedExpr, e2: &mut TypedExpr, m: MetaInfo) -> Result<Type, TypeErrors> {
    let ty = match (&e1.ty, &e2.ty) {
        (ty1, ty2) if ty1 == ty2 => ty1.clone(),
        (Type::Unsigned(UnsignedNumType::Unspecified), Type::Unsigned(ty2)) => {
            check_or_constrain_unsigned(e1, *ty2)?;
            Type::Unsigned(*ty2)
        }
        (Type::Unsigned(ty1), Type::Unsigned(UnsignedNumType::Unspecified)) => {
            check_or_constrain_unsigned(e2, *ty1)?;
            Type::Unsigned(*ty1)
        }
        (Type::Unsigned(UnsignedNumType::Unspecified), Type::Signed(ty2)) => {
            check_or_constrain_signed(e1, *ty2)?;
            Type::Signed(*ty2)
        }
        (Type::Signed(ty1), Type::Unsigned(UnsignedNumType::Unspecified)) => {
            check_or_constrain_signed(e2, *ty1)?;
            Type::Signed(*ty1)
        }
        (Type::Signed(SignedNumType::Unspecified), Type::Signed(ty2)) => {
            check_or_constrain_signed(e1, *ty2)?;
            Type::Signed(*ty2)
        }
        (Type::Signed(ty1), Type::Signed(SignedNumType::Unspecified)) => {
            check_or_constrain_signed(e2, *ty1)?;
            Type::Signed(*ty1)
        }
        _ => {
            let e = TypeErrorEnum::TypeMismatch(e1.ty.clone(), e2.ty.clone());
            return Err(vec![Some(TypeError(e, m))]);
        }
    };
    e1.ty = ty.clone();
    e2.ty = ty.clone();
    Ok(ty)
}
