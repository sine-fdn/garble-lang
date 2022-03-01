//! Evaluates a [`crate::circuit::Circuit`] with inputs supplied by different parties.

use crate::{
    ast::Type,
    circuit::{Circuit, EvalPanic},
    compile::{signed_to_bits, unsigned_to_bits},
    literal::Literal,
    parse::ParseError,
    scan::ScanError,
    token::{SignedNumType, UnsignedNumType},
    typed_ast::Program,
};

/// Evaluates a [`crate::circuit::Circuit`] with inputs supplied by different parties.
pub struct Evaluator {
    circuit: Circuit,
    inputs: Vec<Vec<bool>>,
    output: Option<Vec<Option<bool>>>,
}

impl From<Circuit> for Evaluator {
    fn from(circuit: Circuit) -> Self {
        Self {
            circuit,
            inputs: vec![],
            output: None,
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
    /// An input literal could not be scanned.
    LiteralScanError(Vec<ScanError>),
    /// An input literal could not be parsed.
    LiteralParseError(Vec<ParseError>),
    /// No output has been computed yet.
    OutputHasNotBeenComputed,
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

impl From<EvalPanic> for EvalError {
    fn from(e: EvalPanic) -> Self {
        Self::Panic(e)
    }
}

impl Evaluator {
    /// Evaluates a [`crate::circuit::Circuit`] with the previously set inputs.
    pub fn run(&mut self) -> Result<(), EvalError> {
        if self.inputs.len() != self.circuit.input_gates.len() {
            return Err(EvalError::UnexpectedNumberOfParties);
        }
        for p in 0..self.circuit.input_gates.len() {
            if self.inputs[p].len() != self.circuit.input_gates[p] {
                return Err(EvalError::UnexpectedNumberOfInputsFromParty(p));
            }
        }
        match self.circuit.eval(&self.inputs) {
            Ok(result) => {
                self.inputs.clear();
                self.output = Some(result);
                Ok(())
            }
            Err(e) => {
                self.inputs.clear();
                Err(e.into())
            },
        }
    }

    fn push_input(&mut self) -> &mut Vec<bool> {
        self.inputs.push(vec![]);
        self.inputs.last_mut().unwrap()
    }

    fn get_output(&self) -> Result<Vec<bool>, EvalError> {
        if let Some(output) = &self.output {
            let mut output_bits = Vec::with_capacity(self.circuit.output_gates.len());
            for output_gate in &self.circuit.output_gates {
                output_bits.push(output[*output_gate].unwrap());
            }
            Ok(output_bits)
        } else {
            Err(EvalError::OutputHasNotBeenComputed)
        }
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
    pub fn set_literal(&mut self, checked: &Program, literal: Literal) {
        self.inputs.push(vec![]);
        self.inputs
            .last_mut()
            .unwrap()
            .extend(literal.as_bits(checked));
    }

    /// Decodes the evaluated result as a bool.
    pub fn get_bool(&self) -> Result<bool, EvalError> {
        let output = self.get_output()?;
        if output.len() == 1 {
            Ok(output[0])
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: Type::Bool,
                actual_bits: output.len(),
            })
        }
    }

    /// Decodes the evaluated result as a usize int.
    pub fn get_usize(&self) -> Result<usize, EvalError> {
        self.get_unsigned(Type::Unsigned(UnsignedNumType::Usize))
            .map(|n| n as usize)
    }

    /// Decodes the evaluated result as a u8 int.
    pub fn get_u8(&self) -> Result<u8, EvalError> {
        self.get_unsigned(Type::Unsigned(UnsignedNumType::U8))
            .map(|n| n as u8)
    }

    /// Decodes the evaluated result as a u16 int.
    pub fn get_u16(&self) -> Result<u16, EvalError> {
        self.get_unsigned(Type::Unsigned(UnsignedNumType::U16))
            .map(|n| n as u16)
    }

    /// Decodes the evaluated result as a u32 int.
    pub fn get_u32(&self) -> Result<u32, EvalError> {
        self.get_unsigned(Type::Unsigned(UnsignedNumType::U32))
            .map(|n| n as u32)
    }

    /// Decodes the evaluated result as a u64 int.
    pub fn get_u64(&self) -> Result<u64, EvalError> {
        self.get_unsigned(Type::Unsigned(UnsignedNumType::U64))
            .map(|n| n as u64)
    }

    /// Decodes the evaluated result as a u128 int.
    pub fn get_u128(&self) -> Result<u128, EvalError> {
        self.get_unsigned(Type::Unsigned(UnsignedNumType::U128))
    }

    /// Decodes the evaluated result as a i8 int.
    pub fn get_i8(&self) -> Result<i8, EvalError> {
        self.get_signed(Type::Signed(SignedNumType::I8))
            .map(|n| n as i8)
    }

    /// Decodes the evaluated result as a i16 int.
    pub fn get_i16(&self) -> Result<i16, EvalError> {
        self.get_signed(Type::Signed(SignedNumType::I16))
            .map(|n| n as i16)
    }

    /// Decodes the evaluated result as a i32 int.
    pub fn get_i32(&self) -> Result<i32, EvalError> {
        self.get_signed(Type::Signed(SignedNumType::I32))
            .map(|n| n as i32)
    }

    /// Decodes the evaluated result as a i64 int.
    pub fn get_i64(&self) -> Result<i64, EvalError> {
        self.get_signed(Type::Signed(SignedNumType::I64))
            .map(|n| n as i64)
    }

    /// Decodes the evaluated result as a i128 int.
    pub fn get_i128(&self) -> Result<i128, EvalError> {
        self.get_signed(Type::Signed(SignedNumType::I128))
    }

    /// Decodes the evaluated result as a literal (with enums looked up in the program).
    pub fn get_literal(&self, checked: &Program, ty: &Type) -> Result<Literal, EvalError> {
        let output = self.get_output()?;
        let size = ty.size_in_bits_for_defs(Some(&checked.enum_defs));
        if output.len() == size {
            let bits: Vec<bool> = output.iter().copied().take(size).collect();
            Ok(Literal::from_bits(checked, ty, &bits)?)
        } else {
            Err(EvalError::OutputTypeMismatch {
                expected: ty.clone(),
                actual_bits: output.len(),
            })
        }
    }

    fn get_unsigned(&self, ty: Type) -> Result<u128, EvalError> {
        let output = self.get_output()?;
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

    fn get_signed(&self, ty: Type) -> Result<i128, EvalError> {
        let output = self.get_output()?;
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
}
