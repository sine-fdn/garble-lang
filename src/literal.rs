//! A subset of [`crate::ast::Expr`] that is used as input / output by an
//! [`crate::eval::Evaluator`].
//!
//! See [`crate::literal::Literal`] for examples on how to (de-)serialize to/from Garble literals
//! using `serde`.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

#[cfg(feature = "json_schema")]
use schemars::JsonSchema;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{
    ast::{Expr, ExprEnum, Type, Variant, VariantExprEnum},
    check::{check_type, Defs, TopLevelTypes, TypeError, TypedFns},
    circuit::EvalPanic,
    compile::{
        self, enum_max_size, enum_tag_number, enum_tag_size, signed_to_bits, unsigned_to_bits,
    },
    env::Env,
    eval::EvalError,
    scan::scan,
    token::{SignedNumType, UnsignedNumType},
    CompileTimeError, TypedExpr, TypedProgram,
};

/// A subset of [`crate::ast::Expr`] that is used as input / output by an
/// [`crate::eval::Evaluator`].
///
/// If the `serde` crate feature is enabled, literals can be (de-)serialized to any format supported
/// by `serde`. The following ABNF grammar shows how literals are represented when serialized using
/// `serde_json`:
///
/// ```asci
/// literal = "\"True\"" /
///           "\"False\"" /
///           "{\"NumUnsigned\":[" uint "," uint-ty "]}" /
///           "{\"NumSigned\":[" int "," int-ty "]}" /
///           "{\"ArrayRepeat\":[" literal "," uint "]}" /
///           "{\"Array\":[" [literal *("," literal)] "]}" /
///           "{\"Tuple\":[" [literal *("," literal)] "]}" /
///           "{\"Enum\":[\"" string "\",\"" string "\"," variant "]}" /
///           "{\"Range\":[" uint "," uint "," uint-type "]}"
///
/// uint    = 1*DIGIT
///
/// uint-ty = "\"Usize\"" /
///           "\"U8\"" /
///           "\"U16\"" /
///           "\"U32\"" /
///           "\"U64\"" /
///           "\"Unspecified\""
///
/// int     = ["-"] uint
///
/// int-ty  = "\"I8\"" /
///           "\"I16\"" /
///           "\"I32\"" /
///           "\"I64\"" /
///           "\"Unspecified\""
///
/// string  = 1*ALPHA
///
/// variant = "\"Unit\"" /
///           "{\"Tuple\":[" [literal *("," literal)] "]}"
/// ```
///
/// Here are some example Garble literals and how they would be serialized as JSON:
///
/// | Garble Literal                   | Serialized as JSON                                       |
/// | -------------------------------- | -------------------------------------------------------- |
/// | `true`                           | `"True"`                                                 |
/// | `200u32`                         | `{"NumUnsigned":[200,"U32"]}`                            |
/// | `-200`                           | `{"NumSigned":[-200,"Unspecified"]}`                     |
/// | `[true; 3]`                      | `{"ArrayRepeat":["True",3]}`                             |
/// | `[true, false]`                  | `{"Array":["True","False"]}`                             |
/// | `(true, false, 10)`              | `{"Tuple":["True","False",{"NumUnsigned":[10,"U8"]}]}`   |
/// | `FooBar {foo: true, bar: false}` | `{"Struct":["FooBar",[["foo","True"],["bar","False"]]]}` |
/// | `FooBar::Foo`                    | `{"Enum":["FooBar","Foo","Unit"]}`                       |
/// | `FooBar::Bar(true, false)`       | `{"Enum":["FooBar","Bar",{"Tuple":["True","False"]}]}`   |
/// | `2u8..10u8`                      | `{"Range":[2,10,"U8"]}`                                  |
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "json_schema", derive(JsonSchema))]
pub enum Literal {
    /// Literal `true`.
    True,
    /// Literal `false`.
    False,
    /// Unsigned number literal.
    NumUnsigned(u64, UnsignedNumType),
    /// Signed number literal.
    NumSigned(i64, SignedNumType),
    /// Array "repeat expression", which specifies 1 element, to be repeated a number of times.
    ArrayRepeat(Box<Literal>, usize),
    /// Array literal which explicitly specifies all of its elements.
    Array(Vec<Literal>),
    /// Tuple literal containing the specified fields.
    Tuple(Vec<Literal>),
    /// Struct literal with the specified fields.
    Struct(String, Vec<(String, Literal)>),
    /// Enum literal of the specified variant, possibly with fields.
    Enum(String, String, VariantLiteral),
    /// Range of numbers from the specified min (inclusive) to the specified max (exclusive).
    Range(u64, u64, UnsignedNumType),
}

/// A variant literal (either of unit type or containing fields), used by [`Literal::Enum`].
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "json_schema", derive(JsonSchema))]
pub enum VariantLiteral {
    /// A unit variant, containing no fields.
    Unit,
    /// A tuple variant, containing positional fields (but can be empty).
    Tuple(Vec<Literal>),
}

impl Literal {
    /// Parses the str as a literal of the specified type, looking up enum defs in the program.
    pub fn parse(
        checked: &TypedProgram,
        ty: &Type,
        literal: &str,
    ) -> Result<Self, CompileTimeError> {
        let mut struct_names = HashSet::with_capacity(checked.struct_defs.len());
        let mut enum_names = HashSet::with_capacity(checked.enum_defs.len());
        struct_names.extend(checked.struct_defs.keys());
        enum_names.extend(checked.enum_defs.keys());
        let top_level_defs = TopLevelTypes {
            struct_names,
            enum_names,
        };
        let mut env = Env::new();
        let mut fns = TypedFns::new();
        let const_types = checked
            .const_defs
            .iter()
            .map(|(n, c)| (n.clone(), c.ty.clone()))
            .collect();
        let defs = Defs::new(&const_types, &checked.struct_defs, &checked.enum_defs);
        let mut expr = scan(literal)?
            .parse_literal()?
            .type_check(&top_level_defs, &mut env, &mut fns, &defs)
            .map_err(|errs| {
                let mut errs: Vec<TypeError> = errs.into_iter().flatten().collect();
                errs.sort();
                errs
            })?;
        check_type(&mut expr, ty)
            .map_err(|errs| errs.into_iter().flatten().collect::<Vec<TypeError>>())?;
        expr.ty = ty.clone();
        Ok(expr.into_literal())
    }

    /// Checks whether the literal is of the specified types, looking up enum defs in the program.
    pub fn is_of_type(&self, checked: &TypedProgram, ty: &Type) -> bool {
        match (self, ty) {
            (Literal::True, Type::Bool) => true,
            (Literal::False, Type::Bool) => true,
            (Literal::NumUnsigned(_, ty1), Type::Unsigned(ty2)) if ty1 == ty2 => true,
            (Literal::NumSigned(_, ty1), Type::Signed(ty2)) if ty1 == ty2 => true,
            (Literal::ArrayRepeat(elem, size1), Type::Array(elem_ty, size2)) => {
                size1 == size2 && elem.is_of_type(checked, elem_ty)
            }
            (Literal::Array(elems), Type::Array(elem_ty, size)) if elems.len() == *size => {
                elems.iter().all(|elem| elem.is_of_type(checked, elem_ty))
            }
            (Literal::Struct(struct_name1, fields), Type::Struct(struct_name2))
                if struct_name1 == struct_name2 =>
            {
                if let Some(struct_def) = checked.struct_defs.get(struct_name1) {
                    if struct_def.fields.len() == fields.len() {
                        let mut struct_def_fields = HashMap::with_capacity(fields.len());
                        for (field_name, field_type) in struct_def.fields.iter() {
                            struct_def_fields.insert(field_name, field_type);
                        }
                        for (field_name, field_literal) in fields.iter() {
                            if let Some(expected_type) = struct_def_fields.get(field_name) {
                                if !field_literal.is_of_type(checked, expected_type) {
                                    return false;
                                }
                            } else {
                                return false;
                            }
                        }
                        return true;
                    }
                }
                false
            }
            (Literal::Tuple(fields1), Type::Tuple(fields2)) if fields1.len() == fields2.len() => {
                fields1
                    .iter()
                    .zip(fields2.iter())
                    .all(|(f, ty)| f.is_of_type(checked, ty))
            }
            (Literal::Enum(enum_name1, variant_name1, fields1), Type::Enum(enum_name2))
                if enum_name1 == enum_name2 =>
            {
                if let Some(enum_def) = checked.enum_defs.get(enum_name1) {
                    if let Some(variant2) = enum_def.get_variant(variant_name1) {
                        if variant_name1 == variant2.variant_name() {
                            match (fields1, variant2) {
                                (VariantLiteral::Unit, Variant::Unit(_)) => return true,
                                (VariantLiteral::Tuple(fields1), Variant::Tuple(_, fields2)) => {
                                    return fields1
                                        .iter()
                                        .zip(fields2.iter())
                                        .all(|(f, ty)| f.is_of_type(checked, ty));
                                }
                                _ => return false,
                            }
                        }
                    }
                }
                false
            }
            (Literal::Range(min, max, num_ty), Type::Array(elem_ty, size)) => {
                elem_ty.as_ref() == &Type::Unsigned(*num_ty) && max - min == *size as u64
            }
            _ => false,
        }
    }

    /// Decodes the bits as a panic or literal of the specified type, looking up enum defs in the
    /// program.
    ///
    /// `bits` must include the _panic portion of the circuit_, meaning all wires carrying panic
    /// information must be included in the bits.
    pub fn from_result_bits(
        checked: &TypedProgram,
        ty: &Type,
        bits: &[bool],
        const_sizes: &HashMap<String, usize>,
    ) -> Result<Self, EvalError> {
        match EvalPanic::parse(bits) {
            Ok(bits) => Literal::from_unwrapped_bits(checked, ty, bits, const_sizes),
            Err(panic) => Err(EvalError::Panic(panic)),
        }
    }

    /// Decodes the bits as a literal of the specified type, looking up enum defs in the program.
    ///
    /// `bits` must be the _non-panic output-only portion of the circuit_, meaning all wires
    /// carrying panic information must already have been removed prior to parsing the bits. If you
    /// want to parse a circuit output that might have panicked, use
    /// [`Literal::from_result_bits`] instead.
    pub fn from_unwrapped_bits(
        checked: &TypedProgram,
        ty: &Type,
        bits: &[bool],
        const_sizes: &HashMap<String, usize>,
    ) -> Result<Self, EvalError> {
        match ty {
            Type::Bool => {
                if bits.len() == 1 {
                    if bits[0] {
                        Ok(Literal::True)
                    } else {
                        Ok(Literal::False)
                    }
                } else {
                    Err(EvalError::OutputTypeMismatch {
                        expected: ty.clone(),
                        actual_bits: bits.len(),
                    })
                }
            }
            Type::Unsigned(unsigned_ty) => {
                let size = ty.size_in_bits_for_defs(checked, const_sizes);
                if bits.len() == size {
                    let mut n = 0;
                    for (i, output) in bits.iter().copied().enumerate() {
                        n |= (output as u64) << (size - 1 - i);
                    }
                    Ok(Literal::NumUnsigned(n, *unsigned_ty))
                } else {
                    Err(EvalError::OutputTypeMismatch {
                        expected: ty.clone(),
                        actual_bits: bits.len(),
                    })
                }
            }
            Type::Signed(signed_ty) => {
                let size = ty.size_in_bits_for_defs(checked, const_sizes);
                if bits.len() == size {
                    let mut n = 0;
                    for (i, output) in bits.iter().copied().enumerate() {
                        n |= (output as i64) << (size - 1 - i);
                    }
                    let n = match size {
                        8 => (n as i8) as i64,
                        16 => (n as i16) as i64,
                        32 => (n as i32) as i64,
                        _ => n,
                    };
                    Ok(Literal::NumSigned(n, *signed_ty))
                } else {
                    Err(EvalError::OutputTypeMismatch {
                        expected: ty.clone(),
                        actual_bits: bits.len(),
                    })
                }
            }
            Type::Array(ty, size) => {
                let ty_size = ty.size_in_bits_for_defs(checked, const_sizes);
                let mut elems = vec![];
                let mut i = 0;
                for _ in 0..*size {
                    let bits = &bits[i..i + ty_size];
                    elems.push(Literal::from_unwrapped_bits(
                        checked,
                        ty,
                        bits,
                        const_sizes,
                    )?);
                    i += ty_size;
                }
                Ok(Literal::Array(elems))
            }
            Type::ArrayConst(ty, size) => {
                let size = const_sizes.get(size).unwrap();
                let ty_size = ty.size_in_bits_for_defs(checked, const_sizes);
                let mut elems = vec![];
                let mut i = 0;
                for _ in 0..*size {
                    let bits = &bits[i..i + ty_size];
                    elems.push(Literal::from_unwrapped_bits(
                        checked,
                        ty,
                        bits,
                        const_sizes,
                    )?);
                    i += ty_size;
                }
                Ok(Literal::Array(elems))
            }
            Type::ArrayConstExpr(ty, size_expr) => {
                let const_sizes_u64 = const_sizes
                    .iter()
                    .map(|(k, v)| (k.clone(), *v as u64))
                    .collect();
                let size = compile::resolve_const_expr_unsigned(size_expr, &const_sizes_u64);
                let ty_size = ty.size_in_bits_for_defs(checked, const_sizes);
                let mut elems = vec![];
                let mut i = 0;
                for _ in 0..size {
                    let bits = &bits[i..i + ty_size];
                    elems.push(Literal::from_unwrapped_bits(
                        checked,
                        ty,
                        bits,
                        const_sizes,
                    )?);
                    i += ty_size;
                }
                Ok(Literal::Array(elems))
            }
            Type::Tuple(field_types) => {
                let mut fields = vec![];
                let mut i = 0;
                for ty in field_types {
                    let ty_size = ty.size_in_bits_for_defs(checked, const_sizes);
                    let bits = &bits[i..i + ty_size];
                    fields.push(Literal::from_unwrapped_bits(
                        checked,
                        ty,
                        bits,
                        const_sizes,
                    )?);
                    i += ty_size;
                }
                Ok(Literal::Tuple(fields))
            }
            Type::Struct(struct_name) => {
                let mut fields = vec![];
                let mut i = 0;
                let struct_def = checked.struct_defs.get(struct_name).unwrap();
                for (field_name, ty) in struct_def.fields.iter() {
                    let ty_size = ty.size_in_bits_for_defs(checked, const_sizes);
                    let bits = &bits[i..i + ty_size];
                    let value = Literal::from_unwrapped_bits(checked, ty, bits, const_sizes)?;
                    fields.push((field_name.clone(), value));
                    i += ty_size;
                }
                Ok(Literal::Struct(struct_name.clone(), fields))
            }
            Type::Enum(enum_name) => {
                let enum_def = checked.enum_defs.get(enum_name).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let mut tag_number = 0;
                for (i, output) in bits.iter().copied().take(tag_size).enumerate() {
                    tag_number += (output as usize) << (tag_size - 1 - i);
                }
                let variant = &enum_def.variants[tag_number];
                match variant {
                    Variant::Unit(variant_name) => Ok(Literal::Enum(
                        enum_name.clone(),
                        variant_name.clone(),
                        VariantLiteral::Unit,
                    )),
                    Variant::Tuple(variant_name, field_types) => {
                        let mut fields = Vec::with_capacity(field_types.len());
                        let mut i = tag_size;
                        for ty in field_types {
                            let field = Literal::from_unwrapped_bits(
                                checked,
                                ty,
                                &bits[i..i + ty.size_in_bits_for_defs(checked, const_sizes)],
                                const_sizes,
                            )?;
                            fields.push(field);
                            i += ty.size_in_bits_for_defs(checked, const_sizes);
                        }
                        let variant = VariantLiteral::Tuple(fields);
                        Ok(Literal::Enum(
                            enum_name.clone(),
                            variant_name.clone(),
                            variant,
                        ))
                    }
                }
            }
            Type::Fn(_, _) => panic!("Fn types cannot be directly mapped to bits"),
            Type::UntypedTopLevelDefinition(name, _) => {
                panic!("Untyped top level type '{name}' should have been typechecked at this point")
            }
        }
    }

    /// Encodes the literal as bits, looking up enum defs in the program.
    pub fn as_bits(
        &self,
        checked: &TypedProgram,
        const_sizes: &HashMap<String, usize>,
    ) -> Vec<bool> {
        match self {
            Literal::True => vec![true],
            Literal::False => vec![false],
            Literal::NumUnsigned(n, ty) => {
                let size = Type::Unsigned(*ty).size_in_bits_for_defs(checked, const_sizes);
                let mut bits = vec![];
                unsigned_to_bits(*n, size, &mut bits);
                bits
            }
            Literal::NumSigned(n, ty) => {
                let size = Type::Signed(*ty).size_in_bits_for_defs(checked, const_sizes);
                let mut bits = vec![];
                signed_to_bits(*n, size, &mut bits);
                bits
            }
            Literal::ArrayRepeat(elem, size) => {
                let elem = elem.as_bits(checked, const_sizes);
                let elem_size = elem.len();
                let mut bits = vec![false; elem_size * size];
                for i in 0..*size {
                    bits[(i * elem_size)..(i * elem_size) + elem_size].copy_from_slice(&elem);
                }
                bits
            }
            Literal::Array(elems) => {
                let mut bits = vec![];
                for elem in elems {
                    bits.extend(elem.as_bits(checked, const_sizes))
                }
                bits
            }
            Literal::Tuple(fields) => {
                let mut bits = vec![];
                for f in fields {
                    bits.extend(f.as_bits(checked, const_sizes))
                }
                bits
            }
            Literal::Struct(_, fields) => {
                let mut bits = vec![];
                for (_, f) in fields {
                    bits.extend(f.as_bits(checked, const_sizes))
                }
                bits
            }
            Literal::Enum(enum_name, variant_name, variant) => {
                let enum_def = checked.enum_defs.get(enum_name).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let max_size = enum_max_size(enum_def, checked, const_sizes);
                let mut wires = vec![false; max_size];
                let tag_number = enum_tag_number(enum_def, variant_name);
                for (i, wire) in wires.iter_mut().enumerate().take(tag_size) {
                    *wire = (tag_number >> (tag_size - i - 1)) & 1 == 1;
                }
                let mut w = tag_size;
                match variant {
                    VariantLiteral::Unit => {}
                    VariantLiteral::Tuple(fields) => {
                        for f in fields {
                            let f = f.as_bits(checked, const_sizes);
                            wires[w..w + f.len()].copy_from_slice(&f);
                            w += f.len();
                        }
                    }
                }
                wires
            }
            Literal::Range(min, max, num_ty) => {
                let elems: Vec<usize> = (*min as usize..*max as usize).collect();
                let elem_size = Type::Unsigned(*num_ty).size_in_bits_for_defs(checked, const_sizes);
                let mut bits = Vec::with_capacity(elems.len() * elem_size);
                for elem in elems {
                    unsigned_to_bits(elem as u64, elem_size, &mut bits);
                }
                bits
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::True => write!(f, "true"),
            Literal::False => write!(f, "false"),
            Literal::NumUnsigned(n, _) => write!(f, "{n}"),
            Literal::NumSigned(n, _) => {
                write!(f, "{n}")
            }
            Literal::ArrayRepeat(elem, size) => write!(f, "[{elem}; {size}]"),
            Literal::Array(elems) => {
                write!(f, "[")?;
                let mut elems = elems.iter();
                if let Some(first_elem) = elems.next() {
                    write!(f, "{first_elem}")?;
                }
                for elem in elems {
                    write!(f, ", {elem}")?;
                }
                write!(f, "]")
            }
            Literal::Tuple(fields) => {
                write!(f, "(")?;
                let mut fields = fields.iter();
                if let Some(first_field) = fields.next() {
                    write!(f, "{first_field}")?;
                }
                for field in fields {
                    write!(f, ", {field}")?;
                }
                write!(f, ")")
            }
            Literal::Struct(struct_name, fields) => {
                write!(f, "{struct_name} {{")?;
                let mut fields = fields.iter();
                if let Some((first_field_name, first_field_value)) = fields.next() {
                    write!(f, "{first_field_name}: {first_field_value}")?;
                }
                for (field_name, field_value) in fields {
                    write!(f, ", {field_name}: {field_value}")?;
                }
                write!(f, "}}")
            }
            Literal::Enum(enum_name, variant_name, variant) => match variant {
                VariantLiteral::Unit => write!(f, "{enum_name}::{variant_name}"),
                VariantLiteral::Tuple(fields) => {
                    write!(f, "{enum_name}::{variant_name}")?;
                    write!(f, "(")?;
                    let mut fields = fields.iter();
                    if let Some(first_field) = fields.next() {
                        write!(f, "{first_field}")?;
                    }
                    for field in fields {
                        write!(f, ", {field}")?;
                    }
                    write!(f, ")")
                }
            },
            Literal::Range(min, max, num_ty) => {
                write!(f, "{min}{num_ty}..{max}{num_ty}")
            }
        }
    }
}

impl TypedExpr {
    fn into_literal(self) -> Literal {
        let Expr {
            inner: expr_enum,
            ty,
            ..
        } = self;
        match expr_enum {
            ExprEnum::True => Literal::True,
            ExprEnum::False => Literal::False,
            ExprEnum::NumUnsigned(n, _) => {
                if let Type::Unsigned(ty) = ty {
                    Literal::NumUnsigned(n, ty)
                } else if let Type::Signed(ty) = ty {
                    Literal::NumSigned(n as i64, ty)
                } else {
                    panic!("Literal type is not a number type: {ty:?}")
                }
            }
            ExprEnum::NumSigned(n, _) => {
                if let Type::Unsigned(ty) = ty {
                    Literal::NumUnsigned(n as u64, ty)
                } else if let Type::Signed(ty) = ty {
                    Literal::NumSigned(n, ty)
                } else {
                    panic!("Literal type is not a number type: {ty:?}")
                }
            }
            ExprEnum::ArrayRepeatLiteral(elem, size) => {
                Literal::ArrayRepeat(Box::new(elem.into_literal()), size)
            }
            ExprEnum::ArrayLiteral(elems) => {
                Literal::Array(elems.into_iter().map(|e| e.into_literal()).collect())
            }
            ExprEnum::TupleLiteral(fields) => {
                Literal::Tuple(fields.into_iter().map(|f| f.into_literal()).collect())
            }
            ExprEnum::StructLiteral(struct_name, fields) => Literal::Struct(
                struct_name,
                fields
                    .into_iter()
                    .map(|(name, value)| (name, value.into_literal()))
                    .collect(),
            ),
            ExprEnum::EnumLiteral(name, variant_name, variant) => {
                let variant = match variant {
                    VariantExprEnum::Unit => VariantLiteral::Unit,
                    VariantExprEnum::Tuple(fields) => VariantLiteral::Tuple(
                        fields.into_iter().map(|f| f.into_literal()).collect(),
                    ),
                };
                Literal::Enum(name, variant_name.clone(), variant)
            }
            ExprEnum::Range(min, max, num_ty) => Literal::Range(min, max, num_ty),
            _ => unreachable!("This should result in a literal parse error instead"),
        }
    }
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        if b {
            Literal::True
        } else {
            Literal::False
        }
    }
}

impl From<u8> for Literal {
    fn from(n: u8) -> Self {
        Literal::NumUnsigned(n as u64, UnsignedNumType::U8)
    }
}

impl From<u16> for Literal {
    fn from(n: u16) -> Self {
        Literal::NumUnsigned(n as u64, UnsignedNumType::U16)
    }
}

impl From<u32> for Literal {
    fn from(n: u32) -> Self {
        Literal::NumUnsigned(n as u64, UnsignedNumType::U32)
    }
}

impl From<u64> for Literal {
    fn from(n: u64) -> Self {
        Literal::NumUnsigned(n, UnsignedNumType::U64)
    }
}

impl From<usize> for Literal {
    fn from(value: usize) -> Self {
        Literal::NumUnsigned(value as u64, UnsignedNumType::Usize)
    }
}

impl From<i8> for Literal {
    fn from(n: i8) -> Self {
        Literal::NumSigned(n as i64, SignedNumType::I8)
    }
}

impl From<i16> for Literal {
    fn from(n: i16) -> Self {
        Literal::NumSigned(n as i64, SignedNumType::I16)
    }
}

impl From<i32> for Literal {
    fn from(n: i32) -> Self {
        Literal::NumSigned(n as i64, SignedNumType::I32)
    }
}

impl From<i64> for Literal {
    fn from(n: i64) -> Self {
        Literal::NumSigned(n, SignedNumType::I64)
    }
}

/// Macro to implement From<(A,)> for Literal for different tuple sizes
macro_rules! impl_from_for_tuple {
    ($($el:ident),+) => {
        impl<$($el: Into<Literal>),+> From<($($el),+,)> for Literal {
            #[allow(non_snake_case)]
            fn from(($($el),*,): ($($el),*,)) -> Self {
                Literal::Tuple(vec![$($el.into()),*])
            }
        }
    };
}

impl_from_for_tuple!(A);
impl_from_for_tuple!(A, B);
impl_from_for_tuple!(A, B, C);
impl_from_for_tuple!(A, B, C, D);

impl<const N: usize, T: Into<Literal>> From<[T; N]> for Literal {
    fn from(value: [T; N]) -> Self {
        Literal::Array(value.into_iter().map(Into::into).collect())
    }
}

impl<const N: usize, T> From<&[T; N]> for Literal
where
    T: Clone + Into<Literal>,
{
    fn from(value: &[T; N]) -> Self {
        Literal::Array(value.iter().cloned().map(Into::into).collect())
    }
}

impl<T: Into<Literal>> From<Vec<T>> for Literal {
    fn from(value: Vec<T>) -> Self {
        Literal::Array(value.into_iter().map(Into::into).collect())
    }
}

impl<T> From<&[T]> for Literal
where
    T: Clone + Into<Literal>,
{
    fn from(value: &[T]) -> Self {
        Literal::Array(value.iter().cloned().map(Into::into).collect())
    }
}
