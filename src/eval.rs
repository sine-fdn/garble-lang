use crate::{
    ast::Type,
    circuit::{Circuit, Party},
    compile::{signed_to_bits, unsigned_to_bits},
};

pub struct Computation {
    circuit: Circuit,
    in_a: Vec<bool>,
    in_b: Vec<bool>,
    output: Option<Vec<Option<bool>>>,
}

impl From<Circuit> for Computation {
    fn from(circuit: Circuit) -> Self {
        Self {
            circuit,
            in_a: vec![],
            in_b: vec![],
            output: None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ComputeError {
    UnexpectedNumberOfInputsFromPartyA(usize),
    UnexpectedNumberOfInputsFromPartyB(usize),
    OutputHasNotBeenComputed,
    OutputTypeMismatch { expected: Type, actual_bits: usize },
}

impl Computation {
    pub fn run(&mut self) -> Result<(), ComputeError> {
        let mut expected_in_a_len = 0;
        let mut expected_in_b_len = 0;
        for party in self.circuit.input_gates.iter() {
            match party {
                Party::A => expected_in_a_len += 1,
                Party::B => expected_in_b_len += 1,
            }
        }
        if self.in_a.len() != expected_in_a_len {
            return Err(ComputeError::UnexpectedNumberOfInputsFromPartyA(
                self.in_a.len(),
            ));
        }
        if self.in_b.len() != expected_in_b_len {
            return Err(ComputeError::UnexpectedNumberOfInputsFromPartyB(
                self.in_b.len(),
            ));
        }
        self.output = Some(self.circuit.eval(&self.in_a, &self.in_b));
        self.in_a.clear();
        self.in_b.clear();
        Ok(())
    }

    fn get_input(&mut self, p: Party) -> &mut Vec<bool> {
        match p {
            Party::A => &mut self.in_a,
            Party::B => &mut self.in_b,
        }
    }

    fn get_output(&self) -> Result<Vec<bool>, ComputeError> {
        if let Some(output) = &self.output {
            let mut output_bits = Vec::with_capacity(self.circuit.output_gates.len());
            for output_gate in &self.circuit.output_gates {
                output_bits.push(output[*output_gate].unwrap());
            }
            Ok(output_bits)
        } else {
            Err(ComputeError::OutputHasNotBeenComputed)
        }
    }

    pub fn set_bool(&mut self, p: Party, b: bool) {
        let inputs = self.get_input(p);
        inputs.push(b);
    }

    pub fn get_bool(&self) -> Result<bool, ComputeError> {
        let output = self.get_output()?;
        if output.len() == 1 {
            Ok(output[0])
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: Type::Bool,
                actual_bits: output.len(),
            })
        }
    }

    pub fn set_usize(&mut self, p: Party, n: usize) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, usize::BITS as usize, inputs);
    }

    pub fn set_u8(&mut self, p: Party, n: u8) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 8, inputs);
    }

    pub fn set_u16(&mut self, p: Party, n: u16) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 16, inputs);
    }

    pub fn set_u32(&mut self, p: Party, n: u32) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 32, inputs);
    }

    pub fn set_u64(&mut self, p: Party, n: u64) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 64, inputs);
    }

    pub fn set_u128(&mut self, p: Party, n: u128) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n, 128, inputs);
    }

    pub fn set_i8(&mut self, p: Party, n: i8) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 8, inputs);
    }

    pub fn set_i16(&mut self, p: Party, n: i16) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 16, inputs);
    }

    pub fn set_i32(&mut self, p: Party, n: i32) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 32, inputs);
    }

    pub fn set_i64(&mut self, p: Party, n: i64) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 64, inputs);
    }

    pub fn set_i128(&mut self, p: Party, n: i128) {
        let inputs = self.get_input(p);
        signed_to_bits(n, 128, inputs);
    }

    fn get_unsigned(&self, ty: Type) -> Result<u128, ComputeError> {
        let output = self.get_output()?;
        let size = ty.size_in_bits();
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().take(size).enumerate() {
                n += (output as u128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    fn get_signed(&self, ty: Type) -> Result<i128, ComputeError> {
        let output = self.get_output()?;
        let size = ty.size_in_bits();
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().enumerate().take(size) {
                n += (output as i128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    pub fn get_usize(&self) -> Result<usize, ComputeError> {
        self.get_unsigned(Type::Usize).map(|n| n as usize)
    }

    pub fn get_u8(&self) -> Result<u8, ComputeError> {
        self.get_unsigned(Type::U8).map(|n| n as u8)
    }

    pub fn get_u16(&self) -> Result<u16, ComputeError> {
        self.get_unsigned(Type::U16).map(|n| n as u16)
    }

    pub fn get_u32(&self) -> Result<u32, ComputeError> {
        self.get_unsigned(Type::U32).map(|n| n as u32)
    }

    pub fn get_u64(&self) -> Result<u64, ComputeError> {
        self.get_unsigned(Type::U64).map(|n| n as u64)
    }

    pub fn get_u128(&self) -> Result<u128, ComputeError> {
        self.get_unsigned(Type::U128)
    }

    pub fn get_i8(&self) -> Result<i8, ComputeError> {
        self.get_signed(Type::I8).map(|n| n as i8)
    }

    pub fn get_i16(&self) -> Result<i16, ComputeError> {
        self.get_signed(Type::I16).map(|n| n as i16)
    }

    pub fn get_i32(&self) -> Result<i32, ComputeError> {
        self.get_signed(Type::I32).map(|n| n as i32)
    }

    pub fn get_i64(&self) -> Result<i64, ComputeError> {
        self.get_signed(Type::I64).map(|n| n as i64)
    }

    pub fn get_i128(&self) -> Result<i128, ComputeError> {
        self.get_signed(Type::I128)
    }
}
