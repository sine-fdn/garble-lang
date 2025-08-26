//! Evaluates a [`crate::circuit::Circuit`] with inputs supplied by different parties.

use std::{collections::HashMap, fmt::Debug};

use crate::{
    ast::Type,
    circuit::{EvalPanic, USIZE_BITS},
    compile::{resolve_const_expr_usize, signed_to_bits, unsigned_to_bits},
    literal::Literal,
    token::{SignedNumType, UnsignedNumType},
    CircuitType, CompileTimeError, TypedFnDef, TypedProgram,
};

/// Evaluates a [`crate::circuit::Circuit`] with inputs supplied by different parties.
pub struct Evaluator<'a> {
    /// The type-checked program.
    pub program: &'a TypedProgram,
    /// The function to be evaluated.
    pub main_fn: &'a TypedFnDef,
    /// The compiled circuit.
    pub circuit: &'a CircuitType,
    inputs: Vec<Vec<bool>>,
    const_sizes: &'a HashMap<String, usize>,
}

impl<'a> Evaluator<'a> {
    /// Scans, parses, type-checks and then compiles a program for later evaluation.
    pub fn new(
        program: &'a TypedProgram,
        main_fn: &'a TypedFnDef,
        circuit: &'a CircuitType,
        const_sizes: &'a HashMap<String, usize>,
    ) -> Self {
        Self {
            program,
            main_fn,
            circuit,
            inputs: vec![],
            const_sizes,
        }
    }
}

/// Errors that can occur during evaluation of the circuit.
#[derive(Debug, Clone)]
pub enum EvalError {
    /// The number of input parties does not match the circuit description.
    UnexpectedNumberOfParties,
    /// The input bits of the specified party does not match the circuit description.
    UnexpectedNumberOfInputsFromParty(usize),
    /// An input literal could not be parsed.
    LiteralParseError(CompileTimeError),
    /// The circuit does not have an input argument with the given index.
    InvalidArgIndex(usize),
    /// The literal is not of the expected parameter type.
    InvalidLiteralType(Box<Literal>, Box<Type>),
    /// The number of output bits does not match the expected type.
    OutputTypeMismatch {
        /// The expected output type.
        expected: Type,
        /// The number of output bits.
        actual_bits: usize,
    },
    /// The evaluation panicked, for example due to an integer overflow or div by zero.
    Panic(EvalPanic),
}

impl std::error::Error for EvalError {}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalError::UnexpectedNumberOfParties => f.write_str(
                "The number of provided inputs does not match the expected number of parties of the circuit",
            ),
            EvalError::UnexpectedNumberOfInputsFromParty(party) => f.write_fmt(format_args!("Unexpected number of input bits from party {party}")),
            EvalError::LiteralParseError(err) => {
                err.fmt(f)
            }
            EvalError::InvalidArgIndex(i) => {
                f.write_fmt(format_args!("The circuit does not an input argument with index {i}"))
            }
            EvalError::InvalidLiteralType(literal, ty) => {
                f.write_fmt(format_args!("The argument literal is not of type {ty}: '{literal}'"))
            }
            EvalError::OutputTypeMismatch {
                expected,
                actual_bits,
            } => {
                f.write_fmt(format_args!("Expected the output to have {expected} bits, but found {actual_bits}"))
            }
            EvalError::Panic(p) => {
                p.fmt(f)
            }
        }
    }
}

impl From<EvalPanic> for EvalError {
    fn from(e: EvalPanic) -> Self {
        Self::Panic(e)
    }
}

impl<'a> Evaluator<'a> {
    /// Evaluates a [`crate::circuit::Circuit`] with the previously set inputs.
    pub fn run(self) -> Result<EvalOutput<'a>, EvalError> {
        if self.inputs.len() != self.circuit.parties() {
            return Err(EvalError::UnexpectedNumberOfParties);
        }
        for (p, input_len) in self.circuit.input_lengths().enumerate() {
            if self.inputs[p].len() != input_len {
                return Err(EvalError::UnexpectedNumberOfInputsFromParty(p));
            }
        }
        let output = self.circuit.eval(&self.inputs);
        Ok(EvalOutput {
            program: self.program,
            main_fn: self.main_fn,
            output,
            const_sizes: self.const_sizes.clone(),
        })
    }

    fn push_input(&mut self) -> &mut Vec<bool> {
        self.inputs.push(vec![]);
        self.inputs.last_mut().unwrap()
    }

    /// Encodes a bool as a bits and sets it as the input from the party.
    pub fn set_bool(&mut self, b: bool) {
        let inputs = self.push_input();
        inputs.push(b);
    }

    /// Encodes a usize int as bits and sets it as the input from the party.
    pub fn set_usize(&mut self, n: usize) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u64, USIZE_BITS, inputs);
    }

    /// Encodes a u8 int as bits and sets it as the input from the party.
    pub fn set_u8(&mut self, n: u8) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u64, 8, inputs);
    }

    /// Encodes a u16 int as bits and sets it as the input from the party.
    pub fn set_u16(&mut self, n: u16) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u64, 16, inputs);
    }

    /// Encodes a u32 int as bits and sets it as the input from the party.
    pub fn set_u32(&mut self, n: u32) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u64, 32, inputs);
    }

    /// Encodes a u64 int as bits and sets it as the input from the party.
    pub fn set_u64(&mut self, n: u64) {
        let inputs = self.push_input();
        unsigned_to_bits(n, 64, inputs);
    }

    /// Encodes a i8 int as bits and sets it as the input from the party.
    pub fn set_i8(&mut self, n: i8) {
        let inputs = self.push_input();
        signed_to_bits(n as i64, 8, inputs);
    }

    /// Encodes a i16 int as bits and sets it as the input from the party.
    pub fn set_i16(&mut self, n: i16) {
        let inputs = self.push_input();
        signed_to_bits(n as i64, 16, inputs);
    }

    /// Encodes a i32 int as bits and sets it as the input from the party.
    pub fn set_i32(&mut self, n: i32) {
        let inputs = self.push_input();
        signed_to_bits(n as i64, 32, inputs);
    }

    /// Encodes a i64 int as bits and sets it as the input from the party.
    pub fn set_i64(&mut self, n: i64) {
        let inputs = self.push_input();
        signed_to_bits(n, 64, inputs);
    }

    /// Encodes a literal (with enums looked up in the program) and sets it as the party's input.
    pub fn set_literal(&mut self, literal: Literal) -> Result<(), EvalError> {
        if self.inputs.len() < self.main_fn.params.len() {
            let ty = &self.main_fn.params[self.inputs.len()].ty;
            let ty = resolve_const_type(ty, self.const_sizes);
            if literal.is_of_type(self.program, &ty) {
                self.inputs.push(vec![]);
                self.inputs
                    .last_mut()
                    .unwrap()
                    .extend(literal.as_bits(self.program, self.const_sizes));
                Ok(())
            } else {
                Err(EvalError::InvalidLiteralType(
                    Box::new(literal),
                    Box::new(ty.clone()),
                ))
            }
        } else {
            Err(EvalError::UnexpectedNumberOfParties)
        }
    }

    /// Parses a literal (with enums looked up in the program) and sets it as the party's input.
    pub fn parse_literal(&mut self, literal: &str) -> Result<(), EvalError> {
        if self.inputs.len() < self.main_fn.params.len() {
            let ty = &self.main_fn.params[self.inputs.len()].ty;
            let ty = resolve_const_type(ty, self.const_sizes);
            let parsed =
                Literal::parse(self.program, &ty, literal).map_err(EvalError::LiteralParseError)?;
            self.set_literal(parsed)?;
            Ok(())
        } else {
            Err(EvalError::UnexpectedNumberOfParties)
        }
    }
}

pub(crate) fn resolve_const_type(ty: &Type, const_sizes: &HashMap<String, usize>) -> Type {
    match ty {
        Type::Fn(params, ret_ty) => Type::Fn(
            params
                .iter()
                .map(|ty| resolve_const_type(ty, const_sizes))
                .collect(),
            Box::new(resolve_const_type(ret_ty, const_sizes)),
        ),
        Type::Array(elem_ty, size) => {
            Type::Array(Box::new(resolve_const_type(elem_ty, const_sizes)), *size)
        }
        Type::ArrayConst(elem_ty, size) => Type::Array(
            Box::new(resolve_const_type(elem_ty, const_sizes)),
            *const_sizes.get(size).unwrap(),
        ),
        Type::ArrayConstExpr(elem_ty, size) => Type::Array(
            Box::new(resolve_const_type(elem_ty, const_sizes)),
            resolve_const_expr_usize(size, const_sizes),
        ),
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|ty| resolve_const_type(ty, const_sizes))
                .collect(),
        ),
        ty => ty.clone(),
    }
}

/// The encoded result of a circuit evaluation.
#[derive(Debug, Clone)]
pub struct EvalOutput<'a> {
    program: &'a TypedProgram,
    main_fn: &'a TypedFnDef,
    output: Vec<bool>,
    const_sizes: HashMap<String, usize>,
}

impl TryFrom<EvalOutput<'_>> for bool {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        let output = EvalPanic::parse(&value.output)?;
        if output.len() == 1 {
            Ok(output[0])
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: Type::Bool,
                actual_bits: output.len(),
            })
        }
    }
}

impl TryFrom<EvalOutput<'_>> for usize {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::Usize))
            .map(|n| n as usize)
    }
}

impl TryFrom<EvalOutput<'_>> for u8 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U8))
            .map(|n| n as u8)
    }
}

impl TryFrom<EvalOutput<'_>> for u16 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U16))
            .map(|n| n as u16)
    }
}

impl TryFrom<EvalOutput<'_>> for u32 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U32))
            .map(|n| n as u32)
    }
}

impl TryFrom<EvalOutput<'_>> for u64 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value.into_unsigned(Type::Unsigned(UnsignedNumType::U64))
    }
}

impl TryFrom<EvalOutput<'_>> for i8 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I8))
            .map(|n| n as i8)
    }
}

impl TryFrom<EvalOutput<'_>> for i16 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I16))
            .map(|n| n as i16)
    }
}

impl TryFrom<EvalOutput<'_>> for i32 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I32))
            .map(|n| n as i32)
    }
}

impl TryFrom<EvalOutput<'_>> for i64 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value.into_signed(Type::Signed(SignedNumType::I64))
    }
}

impl TryFrom<EvalOutput<'_>> for Vec<bool> {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        match EvalPanic::parse(&value.output) {
            Ok(output) => Ok(output.to_vec()),
            Err(panic) => Err(EvalError::Panic(panic)),
        }
    }
}

impl EvalOutput<'_> {
    fn into_unsigned(self, ty: Type) -> Result<u64, EvalError> {
        let output = EvalPanic::parse(&self.output)?;
        let size = ty.size_in_bits_for_defs(self.program, &self.const_sizes);
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().enumerate() {
                n |= (output as u64) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    fn into_signed(self, ty: Type) -> Result<i64, EvalError> {
        let output = EvalPanic::parse(&self.output)?;
        let size = ty.size_in_bits_for_defs(self.program, &self.const_sizes);
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().enumerate() {
                n |= (output as i64) << (size - 1 - i);
            }
            Ok(match size {
                8 => (n as i8) as i64,
                16 => (n as i16) as i64,
                32 => (n as i32) as i64,
                _ => n,
            })
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    /// Decodes the evaluated result as a literal (with enums looked up in the program).
    pub fn into_literal(self) -> Result<Literal, EvalError> {
        let ret_ty = &self.main_fn.ty;
        Literal::from_result_bits(self.program, ret_ty, &self.output, &self.const_sizes)
    }
}
