use std::fmt::Display;

use crate::{
    ast::{Type, Variant},
    check::{expect_type, Defs, TypedFns},
    compile::{enum_max_size, enum_tag_number, enum_tag_size, signed_to_bits, unsigned_to_bits},
    env::Env,
    eval::EvalError,
    scan::scan,
    typed_ast::{Expr, ExprEnum, Program, VariantExpr, VariantExprEnum},
    CompileTimeError,
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Literal {
    True,
    False,
    NumUnsigned(u128, Type),
    NumSigned(i128, Type),
    Array(Box<Literal>, usize),
    Tuple(Vec<Literal>),
    Enum(String, String, VariantLiteral),
    Range(usize, usize),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VariantLiteral {
    Unit,
    Tuple(Vec<Literal>),
}

impl Literal {
    pub fn parse(checked: &Program, ty: &Type, literal: &str) -> Result<Self, CompileTimeError> {
        let mut env = Env::new();
        let mut fns = TypedFns::new();
        let defs = Defs::new(&checked.enum_defs);
        let expr = scan(literal)?
            .parse_literal()?
            .type_check(&mut env, &mut fns, &defs)?;
        expect_type(&expr, ty)?;
        Ok(expr.as_literal())
    }

    pub fn from_bits(checked: &Program, ty: &Type, bits: &[bool]) -> Result<Self, EvalError> {
        match ty {
            Type::Bool => {
                if bits.len() == 1 {
                    if bits[0] == true {
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
            Type::Usize | Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 => {
                let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                if bits.len() == size {
                    let mut n = 0;
                    for (i, output) in bits.iter().copied().take(size).enumerate() {
                        n += (output as u128) << (size - 1 - i);
                    }
                    Ok(Literal::NumUnsigned(n, ty.clone()))
                } else {
                    Err(EvalError::OutputTypeMismatch {
                        expected: ty.clone(),
                        actual_bits: bits.len(),
                    })
                }
            }
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => {
                let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                if bits.len() == size {
                    let mut n = 0;
                    for (i, output) in bits.iter().copied().take(size).enumerate() {
                        n += (output as i128) << (size - 1 - i);
                    }
                    Ok(Literal::NumSigned(n, ty.clone()))
                } else {
                    Err(EvalError::OutputTypeMismatch {
                        expected: ty.clone(),
                        actual_bits: bits.len(),
                    })
                }
            }
            Type::Array(_, _) => {
                todo!()
            }
            Type::Tuple(field_types) => {
                let mut fields = vec![];
                let mut i = 0;
                for ty in field_types {
                    let bits = &bits[i..i + ty.size_in_bits_for_defs(Some(&checked.enum_defs))];
                    fields.push(Literal::from_bits(checked, &ty, bits)?);
                    i += ty.size_in_bits_for_defs(Some(&checked.enum_defs));
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
                            let field = Literal::from_bits(
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

    pub fn as_bits(&self, checked: &Program) -> Vec<bool> {
        match self {
            Literal::True => vec![true],
            Literal::False => vec![false],
            Literal::NumUnsigned(n, ty) => {
                let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                let mut bits = vec![];
                unsigned_to_bits(*n, size, &mut bits);
                bits
            }
            Literal::NumSigned(n, ty) => {
                let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
                let mut bits = vec![];
                signed_to_bits(*n, size, &mut bits);
                bits
            }
            Literal::Array(elem, size) => {
                let elem = elem.as_bits(checked);
                let elem_size = elem.len();
                let mut bits = vec![false; elem_size * size];
                for i in 0..*size {
                    bits[(i * elem_size)..(i * elem_size) + elem_size].copy_from_slice(&elem);
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
            Literal::Range(_, _) => todo!(),
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
            Literal::Array(elem, size) => write!(f, "[{}; {}]", elem, size),
            Literal::Tuple(fields) => {
                write!(f, "(")?;
                let mut fields = fields.iter();
                if let Some(first_field) = fields.next() {
                    write!(f, "{}", first_field)?;
                }
                while let Some(field) = fields.next() {
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
                    while let Some(field) = fields.next() {
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
    fn as_literal(self) -> Literal {
        let Expr(expr_enum, ty, _) = self;
        match expr_enum {
            ExprEnum::True => Literal::True,
            ExprEnum::False => Literal::False,
            ExprEnum::NumUnsigned(n) => Literal::NumUnsigned(n, ty),
            ExprEnum::NumSigned(n) => Literal::NumSigned(n, ty),
            ExprEnum::ArrayLiteral(elem, size) => Literal::Array(Box::new(elem.as_literal()), size),
            ExprEnum::TupleLiteral(fields) => {
                Literal::Tuple(fields.into_iter().map(|f| f.as_literal()).collect())
            }
            ExprEnum::EnumLiteral(name, variant) => {
                let VariantExpr(variant_name, _, _) = &variant.as_ref();
                Literal::Enum(name.clone(), variant_name.clone(), variant.as_literal())
            }
            ExprEnum::Range(min, max) => Literal::Range(min, max),
            _ => unreachable!("This should result in a literal parse error instead"),
        }
    }
}

impl VariantExpr {
    fn as_literal(self) -> VariantLiteral {
        let VariantExpr(_, variant, _) = self;
        match variant {
            VariantExprEnum::Unit => VariantLiteral::Unit,
            VariantExprEnum::Tuple(fields) => {
                VariantLiteral::Tuple(fields.into_iter().map(|f| f.as_literal()).collect())
            }
        }
    }
}
