//! Evaluates a [`crate::circuit::Circuit`] with inputs supplied by different parties.

use std::fmt::Debug;

use crate::{
    ast::Type,
    circuit::{Circuit, EvalPanic},
    compile::{signed_to_bits, unsigned_to_bits},
    literal::Literal,
    token::{SignedNumType, UnsignedNumType},
    typed_ast::Program,
    CompileTimeError,
};

/// Evaluates a [`crate::circuit::Circuit`] with inputs supplied by different parties.
pub struct Evaluator<'a> {
    circuit: &'a Circuit,
    inputs: Vec<Vec<bool>>,
}

impl<'a> From<&'a Circuit> for Evaluator<'a> {
    fn from(circuit: &'a Circuit) -> Self {
        Self {
            circuit,
            inputs: vec![],
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
    /// The literal is not of the expected parameter type.
    InvalidLiteralType(Literal, Type),
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
    pub fn run(self) -> Result<EvalOutput, EvalError> {
        if self.inputs.len() != self.circuit.input_gates.len() {
            return Err(EvalError::UnexpectedNumberOfParties);
        }
        for p in 0..self.circuit.input_gates.len() {
            if self.inputs[p].len() != self.circuit.input_gates[p] {
                return Err(EvalError::UnexpectedNumberOfInputsFromParty(p));
            }
        }
        let output = self.circuit.eval(&self.inputs);
        Ok(EvalOutput(output))
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
        unsigned_to_bits(n as u128, usize::BITS as usize, inputs);
    }

    /// Encodes a u8 int as bits and sets it as the input from the party.
    pub fn set_u8(&mut self, n: u8) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 8, inputs);
    }

    /// Encodes a u16 int as bits and sets it as the input from the party.
    pub fn set_u16(&mut self, n: u16) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 16, inputs);
    }

    /// Encodes a u32 int as bits and sets it as the input from the party.
    pub fn set_u32(&mut self, n: u32) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 32, inputs);
    }

    /// Encodes a u64 int as bits and sets it as the input from the party.
    pub fn set_u64(&mut self, n: u64) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 64, inputs);
    }

    /// Encodes a u128 int as bits and sets it as the input from the party.
    pub fn set_u128(&mut self, n: u128) {
        let inputs = self.push_input();
        unsigned_to_bits(n, 128, inputs);
    }

    /// Encodes a i8 int as bits and sets it as the input from the party.
    pub fn set_i8(&mut self, n: i8) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 8, inputs);
    }

    /// Encodes a i16 int as bits and sets it as the input from the party.
    pub fn set_i16(&mut self, n: i16) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 16, inputs);
    }

    /// Encodes a i32 int as bits and sets it as the input from the party.
    pub fn set_i32(&mut self, n: i32) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 32, inputs);
    }

    /// Encodes a i64 int as bits and sets it as the input from the party.
    pub fn set_i64(&mut self, n: i64) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 64, inputs);
    }

    /// Encodes a i128 int as bits and sets it as the input from the party.
    pub fn set_i128(&mut self, n: i128) {
        let inputs = self.push_input();
        signed_to_bits(n, 128, inputs);
    }

    /// Encodes a literal (with enums looked up in the program) and sets it as the party's input.
    pub fn set_literal(&mut self, checked: &Program, literal: Literal) -> Result<(), EvalError> {
        if self.inputs.len() < checked.main.params.len() {
            let ty = &checked.main.params[self.inputs.len()].1;
            if literal.is_of_type(checked, ty) {
                self.inputs.push(vec![]);
                self.inputs
                    .last_mut()
                    .unwrap()
                    .extend(literal.as_bits(checked));
                Ok(())
            } else {
                Err(EvalError::InvalidLiteralType(literal, ty.clone()))
            }
        } else {
            Err(EvalError::UnexpectedNumberOfParties)
        }
    }

    /// Parses a literal (with enums looked up in the program) and sets it as the party's input.
    pub fn parse_literal(&mut self, checked: &Program, literal: &str) -> Result<(), EvalError> {
        if self.inputs.len() < checked.main.params.len() {
            let ty = &checked.main.params[self.inputs.len()].1;
            let parsed =
                Literal::parse(checked, ty, literal).map_err(EvalError::LiteralParseError)?;
            self.set_literal(checked, parsed)?;
            Ok(())
        } else {
            Err(EvalError::UnexpectedNumberOfParties)
        }
    }
}

/// The encoded result of a circuit evaluation.
#[derive(Debug, Clone)]
pub struct EvalOutput(Vec<bool>);

impl TryFrom<EvalOutput> for bool {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        let output = EvalPanic::parse(&value.0)?;
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

impl TryFrom<EvalOutput> for usize {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::Usize))
            .map(|n| n as usize)
    }
}

impl TryFrom<EvalOutput> for u8 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U8))
            .map(|n| n as u8)
    }
}

impl TryFrom<EvalOutput> for u16 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U16))
            .map(|n| n as u16)
    }
}

impl TryFrom<EvalOutput> for u32 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U32))
            .map(|n| n as u32)
    }
}

impl TryFrom<EvalOutput> for u64 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_unsigned(Type::Unsigned(UnsignedNumType::U64))
            .map(|n| n as u64)
    }
}

impl TryFrom<EvalOutput> for u128 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value.into_unsigned(Type::Unsigned(UnsignedNumType::U128))
    }
}

impl TryFrom<EvalOutput> for i8 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I8))
            .map(|n| n as i8)
    }
}

impl TryFrom<EvalOutput> for i16 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I16))
            .map(|n| n as i16)
    }
}

impl TryFrom<EvalOutput> for i32 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I32))
            .map(|n| n as i32)
    }
}

impl TryFrom<EvalOutput> for i64 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value
            .into_signed(Type::Signed(SignedNumType::I64))
            .map(|n| n as i64)
    }
}

impl TryFrom<EvalOutput> for i128 {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        value.into_signed(Type::Signed(SignedNumType::I128))
    }
}

impl TryFrom<EvalOutput> for Vec<bool> {
    type Error = EvalError;

    fn try_from(value: EvalOutput) -> Result<Self, Self::Error> {
        match EvalPanic::parse(&value.0) {
            Ok(output) => Ok(output.to_vec()),
            Err(panic) => Err(EvalError::Panic(panic)),
        }
    }
}

impl EvalOutput {
    fn into_unsigned(self, ty: Type) -> Result<u128, EvalError> {
        let output = EvalPanic::parse(&self.0)?;
        let size = ty.size_in_bits_for_defs(None);
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().take(size).enumerate() {
                n += (output as u128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    fn into_signed(self, ty: Type) -> Result<i128, EvalError> {
        let output = EvalPanic::parse(&self.0)?;
        let size = ty.size_in_bits_for_defs(None);
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().enumerate().take(size) {
                n += (output as i128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    /// Decodes the evaluated result as a literal (with enums looked up in the program).
    pub fn into_literal(self, checked: &Program) -> Result<Literal, EvalError> {
        Literal::from_result_bits(checked, &checked.main.body.1, &self.0)
    }
}
