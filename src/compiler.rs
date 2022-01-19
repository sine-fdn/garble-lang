use std::{collections::HashMap, cmp::max};

use crate::{
    ast::{Op, ParamDef, Party, Type},
    circuit::{Circuit, Gate, GateIndex},
    env::Env,
    typed_ast::{Expr, ExprEnum, FnDef, Program},
};

impl Program {
    pub fn compile(&self) -> Circuit {
        let mut fns = HashMap::new();
        for fn_def in self.fn_defs.iter() {
            fns.insert(fn_def.identifier.clone(), fn_def);
        }
        let mut env = Env::new();
        let mut gates = vec![];
        let mut wire = 2;
        for (party, ParamDef(identifier, ty)) in self.main.params.iter() {
            let type_size = ty.size_in_bits();
            let mut wires = Vec::with_capacity(type_size);
            for _i in 0..type_size {
                match party {
                    Party::A => gates.push(Gate::InA),
                    Party::B => gates.push(Gate::InB),
                };
                wires.push(wire);
                wire += 1;
            }
            env.set(identifier.clone(), wires);
        }
        let output_gates = self.main.body.compile(&fns, &mut env, &mut gates);
        Circuit {
            gates,
            output_gates,
        }
    }
}

fn push_gate(gates: &mut Vec<Gate>, gate: Gate) -> GateIndex {
    gates.push(gate);
    gates.len() + 1 // because index 0 and 1 are reserved for const true/false
}

fn extend_to_bits(v: &mut Vec<usize>, bits: usize) {
    if v.len() != bits {
        let old_size = v.len();
        v.resize(bits, 0);
        v.copy_within(0..old_size, bits - old_size);
        v[0..old_size].fill(0);
    }
}

impl Expr {
    fn compile(
        &self,
        fns: &HashMap<String, &FnDef>,
        env: &mut Env<Vec<GateIndex>>,
        gates: &mut Vec<Gate>,
    ) -> Vec<GateIndex> {
        let Expr(expr, ty, meta) = self;
        match expr {
            ExprEnum::True => {
                vec![1]
            }
            ExprEnum::False => {
                vec![0]
            }
            ExprEnum::NumUnsigned(n) => {
                let mut bits = Vec::with_capacity(ty.size_in_bits());
                unsigned_to_bits(*n, ty.size_in_bits(), &mut bits);
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::Identifier(s) => env.get(s).unwrap(),
            ExprEnum::Op(op, x, y) => {
                let mut x = x.compile(fns, env, gates);
                let mut y = y.compile(fns, env, gates);
                let bits = max(x.len(), y.len());
                extend_to_bits(&mut x, bits);
                extend_to_bits(&mut y, bits);
                match op {
                    Op::BitAnd => {
                        let mut output_bits = vec![0; bits];
                        for i in 0..bits {
                            output_bits[i] = push_gate(gates, Gate::And(x[i], y[i]));
                        }
                        output_bits
                    }
                    Op::BitXor => {
                        let mut output_bits = vec![0; bits];
                        for i in 0..bits {
                            output_bits[i] = push_gate(gates, Gate::Xor(x[i], y[i]));
                        }
                        output_bits
                    }
                    Op::BitOr => {
                        let mut output_bits = vec![0; bits];
                        for i in 0..bits {
                            let xor = push_gate(gates, Gate::Xor(x[i], y[i]));
                            let and = push_gate(gates, Gate::And(x[i], y[i]));
                            let or = push_gate(gates, Gate::Xor(xor, and));
                            output_bits[i] = or;
                        }
                        output_bits
                    }
                    Op::Add => {
                        let mut carry = 0;
                        let mut sum = vec![0; bits];
                        // sequence of full adders:
                        for i in 0..bits {
                            let i = bits - 1 - i;
                            let x = x[i];
                            let y = y[i];
                            // first half-adder:
                            let u = push_gate(gates, Gate::Xor(x, y));
                            let v = push_gate(gates, Gate::And(x, y));
                            // second half-adder:
                            let s = push_gate(gates, Gate::Xor(u, carry));
                            let w = push_gate(gates, Gate::And(u, carry));
                            sum[i] = s;
                            // or gate:
                            let xor_v_w = push_gate(gates, Gate::Xor(v, w));
                            let and_v_w = push_gate(gates, Gate::And(v, w));
                            let or_v_w = push_gate(gates, Gate::Xor(xor_v_w, and_v_w));
                            carry = or_v_w;
                        }
                        sum
                    }
                    Op::GreaterThan | Op::LessThan => {
                        let mut acc_gt = 0;
                        let mut acc_lt = 0;
                        for i in 0..bits {
                            // greater-than for the current bit:
                            let xor = push_gate(gates, Gate::Xor(x[i], y[i]));
                            let gt = push_gate(gates, Gate::And(xor, x[i]));

                            // less-than for the current bit:
                            let lt = push_gate(gates, Gate::And(xor, y[i]));

                            // greater-than or'ed with accumulator:
                            let xor = push_gate(gates, Gate::Xor(gt, acc_gt));
                            let and = push_gate(gates, Gate::And(gt, acc_gt));
                            let gt = push_gate(gates, Gate::Xor(xor, and));

                            // less-than or'ed with accumulator:
                            let xor = push_gate(gates, Gate::Xor(lt, acc_lt));
                            let and = push_gate(gates, Gate::And(lt, acc_lt));
                            let lt = push_gate(gates, Gate::Xor(xor, and));

                            let not_acc_gt = push_gate(gates, Gate::Xor(acc_gt, 1));
                            let not_acc_lt = push_gate(gates, Gate::Xor(acc_lt, 1));

                            acc_gt = push_gate(gates, Gate::And(gt, not_acc_lt));
                            acc_lt = push_gate(gates, Gate::And(lt, not_acc_gt))
                        }
                        match op {
                            Op::GreaterThan => vec![acc_gt],
                            Op::LessThan => vec![acc_lt],
                            _ => unreachable!(),
                        }
                    }
                    Op::Eq | Op::NotEq => {
                        let mut acc = 1;
                        for i in 0..bits {
                            let xor = push_gate(gates, Gate::Xor(x[i], y[i]));
                            let eq = push_gate(gates, Gate::Xor(xor, 1));
                            acc = push_gate(gates, Gate::And(acc, eq));
                        }
                        match op {
                            Op::Eq => vec![acc],
                            Op::NotEq => vec![push_gate(gates, Gate::Xor(acc, 1))],
                            _ => unreachable!(),
                        }
                    }
                }
            }
            ExprEnum::Let(var, binding, body) => {
                let binding = binding.compile(fns, env, gates);
                env.push();
                env.set(var.clone(), binding);
                let body = body.compile(fns, env, gates);
                env.pop();
                body
            }
            ExprEnum::FnCall(identifier, args) => {
                let fn_def = *fns.get(identifier).unwrap();
                let mut body = fn_def.body.clone();
                for (ParamDef(identifier, ty), arg) in fn_def.params.iter().zip(args) {
                    let let_expr =
                        ExprEnum::Let(identifier.clone(), Box::new(arg.clone()), Box::new(body));
                    body = Expr(let_expr, ty.clone(), meta.clone())
                }
                env.push();
                let body = body.compile(fns, env, gates);
                env.pop();
                body
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.compile(fns, env, gates);
                let case_true = case_true.compile(fns, env, gates);
                let case_false = case_false.compile(fns, env, gates);
                assert_eq!(condition.len(), 1);
                assert_eq!(case_true.len(), case_false.len());
                let condition = condition[0];
                let not_condition = push_gate(gates, Gate::Xor(condition, 1));
                let mut gate_indexes = Vec::with_capacity(case_true.len());
                for i in 0..case_true.len() {
                    let case_true = case_true[i];
                    let case_false = case_false[i];
                    let gate_if_true = push_gate(gates, Gate::And(case_true, condition));
                    let gate_if_false = push_gate(gates, Gate::And(case_false, not_condition));
                    gate_indexes.push(push_gate(gates, Gate::Xor(gate_if_true, gate_if_false)));
                }
                gate_indexes
            }
        }
    }
}

impl Type {
    fn size_in_bits(&self) -> usize {
        match self {
            Type::Bool => 1,
            Type::U8 => 8,
            Type::U16 => 16,
            Type::U32 => 32,
            Type::U64 => 64,
            Type::U128 => 128,
            Type::Fn(_, _) => panic!("Fn types cannot be directly mapped to bits"),
        }
    }
}

pub struct Computation {
    circuit: Circuit,
    in_a: Vec<bool>,
    in_b: Vec<bool>,
    output: Option<Vec<Option<bool>>>,
}

impl Into<Computation> for Circuit {
    fn into(self) -> Computation {
        Computation {
            circuit: self,
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
        for gate in self.circuit.gates.iter() {
            match gate {
                Gate::InA => expected_in_a_len += 1,
                Gate::InB => expected_in_b_len += 1,
                _ => {}
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

    fn get_unsigned(&self, ty: Type) -> Result<u128, ComputeError> {
        let output = self.get_output()?;
        let size = ty.size_in_bits();
        if output.len() == size {
            let mut n = 0;
            for i in 0..size {
                n += (output[i] as u128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
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
}

fn unsigned_to_bits(n: u128, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push((n >> (size - 1 - i) & 1) == 1);
    }
}
