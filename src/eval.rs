use crate::{
    ast::Type,
    circuit::Circuit,
    compile::{signed_to_bits, unsigned_to_bits},
    literal::Literal,
    parse::ParseError,
    scan::ScanError,
    typed_ast::Program,
};

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

#[derive(Debug, Clone)]
pub enum EvalError {
    UnexpectedNumberOfParties,
    UnexpectedNumberOfInputsFromParty(usize),
    LiteralScanError(Vec<ScanError>),
    LiteralParseError(Vec<ParseError>),
    OutputHasNotBeenComputed,
    OutputTypeMismatch { expected: Type, actual_bits: usize },
}

impl Evaluator {
    pub fn run(&mut self) -> Result<(), EvalError> {
        if self.inputs.len() != self.circuit.input_gates.len() {
            return Err(EvalError::UnexpectedNumberOfParties);
        }
        for p in 0..self.circuit.input_gates.len() {
            if self.inputs[p].len() != self.circuit.input_gates[p] {
                return Err(EvalError::UnexpectedNumberOfInputsFromParty(p));
            }
        }
        self.output = Some(self.circuit.eval(&self.inputs));
        self.inputs.clear();
        Ok(())
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

    pub fn set_bool(&mut self, b: bool) {
        let inputs = self.push_input();
        inputs.push(b);
    }

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

    pub fn set_usize(&mut self, n: usize) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, usize::BITS as usize, inputs);
    }

    pub fn set_u8(&mut self, n: u8) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 8, inputs);
    }

    pub fn set_u16(&mut self, n: u16) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 16, inputs);
    }

    pub fn set_u32(&mut self, n: u32) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 32, inputs);
    }

    pub fn set_u64(&mut self, n: u64) {
        let inputs = self.push_input();
        unsigned_to_bits(n as u128, 64, inputs);
    }

    pub fn set_u128(&mut self, n: u128) {
        let inputs = self.push_input();
        unsigned_to_bits(n, 128, inputs);
    }

    pub fn set_i8(&mut self, n: i8) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 8, inputs);
    }

    pub fn set_i16(&mut self, n: i16) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 16, inputs);
    }

    pub fn set_i32(&mut self, n: i32) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 32, inputs);
    }

    pub fn set_i64(&mut self, n: i64) {
        let inputs = self.push_input();
        signed_to_bits(n as i128, 64, inputs);
    }

    pub fn set_i128(&mut self, n: i128) {
        let inputs = self.push_input();
        signed_to_bits(n, 128, inputs);
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

    pub fn get_usize(&self) -> Result<usize, EvalError> {
        self.get_unsigned(Type::Usize).map(|n| n as usize)
    }

    pub fn get_u8(&self) -> Result<u8, EvalError> {
        self.get_unsigned(Type::U8).map(|n| n as u8)
    }

    pub fn get_u16(&self) -> Result<u16, EvalError> {
        self.get_unsigned(Type::U16).map(|n| n as u16)
    }

    pub fn get_u32(&self) -> Result<u32, EvalError> {
        self.get_unsigned(Type::U32).map(|n| n as u32)
    }

    pub fn get_u64(&self) -> Result<u64, EvalError> {
        self.get_unsigned(Type::U64).map(|n| n as u64)
    }

    pub fn get_u128(&self) -> Result<u128, EvalError> {
        self.get_unsigned(Type::U128)
    }

    pub fn get_i8(&self) -> Result<i8, EvalError> {
        self.get_signed(Type::I8).map(|n| n as i8)
    }

    pub fn get_i16(&self) -> Result<i16, EvalError> {
        self.get_signed(Type::I16).map(|n| n as i16)
    }

    pub fn get_i32(&self) -> Result<i32, EvalError> {
        self.get_signed(Type::I32).map(|n| n as i32)
    }

    pub fn get_i64(&self) -> Result<i64, EvalError> {
        self.get_signed(Type::I64).map(|n| n as i64)
    }

    pub fn get_i128(&self) -> Result<i128, EvalError> {
        self.get_signed(Type::I128)
    }

    pub fn set_literal(&mut self, checked: &Program, literal: Literal) {
        self.inputs.push(vec![]);
        self.inputs
            .last_mut()
            .unwrap()
            .extend(literal.as_bits(checked));
    }

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
}
