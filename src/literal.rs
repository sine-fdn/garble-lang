//! A subset of [`crate::typed_ast::Expr`] that is used as input / output by an
//! [`crate::eval::Evaluator`].

use std::fmt::Display;

use crate::{
    ast::{Type, Variant},
    check::{coerce_type, Defs, TypedFns},
    compile::{enum_max_size, enum_tag_number, enum_tag_size, signed_to_bits, unsigned_to_bits},
    env::Env,
    eval::EvalError,
    scan::scan,
    token::{SignedNumType, UnsignedNumType},
    typed_ast::{Expr, ExprEnum, Program, VariantExpr, VariantExprEnum},
    CompileTimeError, circuit::EvalPanic,
};

/// A subset of [`crate::typed_ast::Expr`] that is used as input / output by an
/// [`crate::eval::Evaluator`].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Literal {
    /// Literal `true`.
    True,
    /// Literal `false`.
    False,
    /// Unsigned number literal.
    NumUnsigned(u128, UnsignedNumType),
    /// Signed number literal.
    NumSigned(i128, SignedNumType),
    /// Array "repeat expression", which specifies 1 element, to be repeated a number of times.
    ArrayRepeat(Box<Literal>, usize),
    /// Array literal which explicitly specifies all of its elements.
    Array(Vec<Literal>),
    /// Tuple literal containing the specified fields.
    Tuple(Vec<Literal>),
    /// Enum literal of the specified variant, possibly with fields.
    Enum(String, String, VariantLiteral),
    /// Range of numbers from the specified min (inclusive) to the specified max (exclusive).
    Range(usize, usize),
}

/// A variant literal (either of unit type or containing fields), used by [`Literal::EnumLiteral`].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VariantLiteral {
    /// A unit variant, containing no fields.
    Unit,
    /// A tuple variant, containing positional fields (but can be empty).
    Tuple(Vec<Literal>),
}

impl Literal {
    /// Parses the str as a literal of the specified type, looking up enum defs in the program.
    pub fn parse(checked: &Program, ty: &Type, literal: &str) -> Result<Self, CompileTimeError> {
        let mut env = Env::new();
        let mut fns = TypedFns::new();
        let defs = Defs::new(&checked.enum_defs);
        let mut expr = scan(literal)?
            .parse_literal()?
            .type_check(&mut env, &mut fns, &defs)?;
        coerce_type(&mut expr, ty)?;
        expr.1 = ty.clone();
        Ok(expr.into_literal())
    }

    /// Decodes the bits as a panic or literal of the specified type, looking up enum defs in the
    /// program.
    ///
    /// `bits` must include the _panic portion of the circuit_, meaning all wires carrying panic
    /// information must be included in the bits.
    pub fn from_result_bits(checked: &Program, ty: &Type, bits: &[bool]) -> Result<Self, EvalError> {
        match EvalPanic::parse(bits) {
            Ok(bits) => Literal::from_unwrapped_bits(checked, ty, bits),
            Err(panic) => Err(EvalError::Panic(panic)),
        }
    }

    /// Decodes the bits as a literal of the specified type, looking up enum defs in the program.
    ///
    /// `bits` must be the _non-panic output-only portion of the circuit_, meaning all wires
    /// carrying panic information must already have been removed prior to parsing the bits. If you
    /// want to parse a circuit output that might have panicked, use
    /// [`from_output`] instead.
    pub fn from_unwrapped_bits(checked: &Program, ty: &Type, bits: &[bool]) -> Result<Self, EvalError> {
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
                let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                if bits.len() == size {
                    let mut n = 0;
                    for (i, output) in bits.iter().copied().take(size).enumerate() {
                        n += (output as u128) << (size - 1 - i);
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
                let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                if bits.len() == size {
                    let mut n = 0;
                    for (i, output) in bits.iter().copied().take(size).enumerate() {
                        n += (output as i128) << (size - 1 - i);
                    }
                    Ok(Literal::NumSigned(n, *signed_ty))
                } else {
                    Err(EvalError::OutputTypeMismatch {
                        expected: ty.clone(),
                        actual_bits: bits.len(),
                    })
                }
            }
            Type::Array(ty, size) => {
                let ty_size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                let mut elems = vec![];
                let mut i = 0;
                for _ in 0..*size {
                    let bits = &bits[i..i + ty_size];
                    elems.push(Literal::from_unwrapped_bits(checked, ty, bits)?);
                    i += ty_size;
                }
                Ok(Literal::Array(elems))
            }
            Type::Tuple(field_types) => {
                let mut fields = vec![];
                let mut i = 0;
                for ty in field_types {
                    let ty_size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                    let bits = &bits[i..i + ty_size];
                    fields.push(Literal::from_unwrapped_bits(checked, ty, bits)?);
                    i += ty_size;
                }
                Ok(Literal::Tuple(fields))
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
                                &bits[i..i + ty.size_in_bits_for_defs(Some(&checked.enum_defs))],
                            )?;
                            fields.push(field);
                            i += ty.size_in_bits_for_defs(Some(&checked.enum_defs));
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
        }
    }

    /// Encodes the literal as bits, looking up enum defs in the program.
    pub fn as_bits(&self, checked: &Program) -> Vec<bool> {
        match self {
            Literal::True => vec![true],
            Literal::False => vec![false],
            Literal::NumUnsigned(n, ty) => {
                let size = Type::Unsigned(*ty).size_in_bits_for_defs(Some(&checked.enum_defs));
                let mut bits = vec![];
                unsigned_to_bits(*n, size, &mut bits);
                bits
            }
            Literal::NumSigned(n, ty) => {
                let size = Type::Signed(*ty).size_in_bits_for_defs(Some(&checked.enum_defs));
                let mut bits = vec![];
                signed_to_bits(*n, size, &mut bits);
                bits
            }
            Literal::ArrayRepeat(elem, size) => {
                let elem = elem.as_bits(checked);
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
                    bits.extend(elem.as_bits(checked))
                }
                bits
            }
            Literal::Tuple(fields) => {
                let mut bits = vec![];
                for f in fields {
                    bits.extend(f.as_bits(checked))
                }
                bits
            }
            Literal::Enum(enum_name, variant_name, variant) => {
                let enum_def = checked.enum_defs.get(enum_name).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let max_size = enum_max_size(enum_def, &checked.enum_defs);
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
                            let f = f.as_bits(checked);
                            wires[w..w + f.len()].copy_from_slice(&f);
                            w += f.len();
                        }
                    }
                }
                wires
            }
            Literal::Range(min, max) => {
                let elems: Vec<usize> = (*min..*max).into_iter().collect();
                let elem_size = Type::Unsigned(UnsignedNumType::Usize)
                    .size_in_bits_for_defs(Some(&checked.enum_defs));
                let mut bits = Vec::with_capacity(elems.len() * elem_size);
                for elem in elems {
                    unsigned_to_bits(elem as u128, elem_size, &mut bits);
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
            Literal::NumUnsigned(n, _) => write!(f, "{}", n),
            Literal::NumSigned(n, _) => write!(f, "{}", n),
            Literal::ArrayRepeat(elem, size) => write!(f, "[{}; {}]", elem, size),
            Literal::Array(elems) => {
                write!(f, "[")?;
                let mut elems = elems.iter();
                if let Some(first_elem) = elems.next() {
                    write!(f, "{}", first_elem)?;
                }
                for elem in elems {
                    write!(f, ", {}", elem)?;
                }
                write!(f, "]")
            }
            Literal::Tuple(fields) => {
                write!(f, "(")?;
                let mut fields = fields.iter();
                if let Some(first_field) = fields.next() {
                    write!(f, "{}", first_field)?;
                }
                for field in fields {
                    write!(f, ", {}", field)?;
                }
                write!(f, ")")
            }
            Literal::Enum(enum_name, variant_name, variant) => match variant {
                VariantLiteral::Unit => write!(f, "{}::{}", enum_name, variant_name),
                VariantLiteral::Tuple(fields) => {
                    write!(f, "{}::{}", enum_name, variant_name)?;
                    write!(f, "(")?;
                    let mut fields = fields.iter();
                    if let Some(first_field) = fields.next() {
                        write!(f, "{}", first_field)?;
                    }
                    for field in fields {
                        write!(f, ", {}", field)?;
                    }
                    write!(f, ")")
                }
            },
            Literal::Range(min, max) => write!(f, "{}..{}", min, max),
        }
    }
}

impl Expr {
    fn into_literal(self) -> Literal {
        let Expr(expr_enum, ty, _) = self;
        match expr_enum {
            ExprEnum::True => Literal::True,
            ExprEnum::False => Literal::False,
            ExprEnum::NumUnsigned(n, _) => {
                if let Type::Unsigned(ty) = ty {
                    Literal::NumUnsigned(n, ty)
                } else if let Type::Signed(ty) = ty {
                    Literal::NumSigned(n as i128, ty)
                } else {
                    panic!("Literal type is not a number type: {:?}", ty)
                }
            }
            ExprEnum::NumSigned(n, _) => {
                if let Type::Unsigned(ty) = ty {
                    Literal::NumUnsigned(n as u128, ty)
                } else if let Type::Signed(ty) = ty {
                    Literal::NumSigned(n, ty)
                } else {
                    panic!("Literal type is not a number type: {:?}", ty)
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
            ExprEnum::EnumLiteral(name, variant) => {
                let VariantExpr(variant_name, _, _) = &variant.as_ref();
                Literal::Enum(name, variant_name.clone(), variant.into_literal())
            }
            ExprEnum::Range(min, max) => Literal::Range(min, max),
            _ => unreachable!("This should result in a literal parse error instead"),
        }
    }
}

impl VariantExpr {
    fn into_literal(self) -> VariantLiteral {
        let VariantExpr(_, variant, _) = self;
        match variant {
            VariantExprEnum::Unit => VariantLiteral::Unit,
            VariantExprEnum::Tuple(fields) => {
                VariantLiteral::Tuple(fields.into_iter().map(|f| f.into_literal()).collect())
            }
        }
    }
}
