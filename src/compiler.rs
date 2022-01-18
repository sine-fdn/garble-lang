use std::collections::{HashMap, HashSet};

use crate::{
    ast::{Op, ParamDef, Party, Type},
    circuit::{Circuit, Gate, GateIndex},
    parser::MetaInfo,
    typed_ast::{Expr, ExprEnum, MainDef, Program},
};

impl Program {
    pub fn compile(&self) -> Circuit {
        // TODO: compile non-main fn defs
        let mut bindings = HashMap::new();
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
            bindings.insert(identifier.clone(), wires);
        }
        let mut env = bindings.into();
        let output_gates = self.main.body.compile(&mut env, &mut gates);
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
        println!("before (len {}): {:?}", v.len(), v);
        let old_size = v.len();
        v.resize(bits, 0);
        v.copy_within(0..old_size, bits - old_size);
        v[0..old_size].fill(0);
        println!("after (len {}): {:?}", v.len(), v);
    }
}

impl Expr {
    fn compile(&self, env: &mut Env, gates: &mut Vec<Gate>) -> Vec<GateIndex> {
        let Expr(expr, ty, _meta) = self;
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
            ExprEnum::Identifier(s) => env.get(s),
            ExprEnum::Op(op, x, y) => {
                let mut x = x.compile(env, gates);
                let mut y = y.compile(env, gates);
                match op {
                    Op::BitAnd => {
                        vec![push_gate(gates, Gate::And(x[0], y[0]))]
                    }
                    Op::BitXor => {
                        vec![push_gate(gates, Gate::Xor(x[0], y[0]))]
                    }
                    Op::Add => {
                        match ty {
                            Type::Bool => panic!("Addition is not supported for type Bool"),
                            Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::U128 => {
                                let bits = ty.size_in_bits();
                                let mut carry = 0;
                                let mut sum = vec![0; bits];
                                extend_to_bits(&mut x, bits);
                                extend_to_bits(&mut y, bits);
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
                        }
                    }
                }
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
        }
    }
}

type Bindings = HashMap<String, Vec<GateIndex>>;

struct Env(Vec<Bindings>);

impl Into<Env> for Bindings {
    fn into(self) -> Env {
        Env(vec![self])
    }
}

impl Env {
    fn get(&self, identifier: &str) -> Vec<GateIndex> {
        for bindings in self.0.iter().rev() {
            if let Some(gate) = bindings.get(identifier) {
                return gate.clone();
            }
        }
        panic!("Found identifier without binding: '{}'", identifier);
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
            Err(ComputeError::OutputTypeMismatch{
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

#[test]
fn compile_xor() -> Result<(), ComputeError> {
    let prg = Program {
        fn_defs: vec![],
        main: MainDef {
            params: vec![(Party::A, ParamDef("x".to_string(), Type::Bool))],
            body: Expr(
                ExprEnum::Op(
                    Op::BitXor,
                    Box::new(Expr(
                        ExprEnum::Identifier("x".to_string()),
                        Type::Bool,
                        MetaInfo {},
                    )),
                    Box::new(Expr(ExprEnum::True, Type::Bool, MetaInfo {})),
                ),
                Type::Bool,
                MetaInfo {},
            ),
            meta: MetaInfo {},
        },
    };
    let circuit = prg.compile();
    let mut computation: Computation = circuit.into();
    for b in [true, false] {
        computation.set_bool(Party::A, b);
        computation.run()?;
        assert_eq!(computation.get_bool()?, !b);
    }
    Ok(())
}

#[test]
fn compile_add() -> Result<(), ComputeError> {
    for y in 0..127 {
        let prg = Program {
            fn_defs: vec![],
            main: MainDef {
                params: vec![(Party::A, ParamDef("x".to_string(), Type::U8))],
                body: Expr(
                    ExprEnum::Op(
                        Op::Add,
                        Box::new(Expr(
                            ExprEnum::Identifier("x".to_string()),
                            Type::U8,
                            MetaInfo {},
                        )),
                        Box::new(Expr(ExprEnum::NumUnsigned(y), Type::U8, MetaInfo {})),
                    ),
                    Type::U8,
                    MetaInfo {},
                ),
                meta: MetaInfo {},
            },
        };
        let circuit = prg.compile();
        let mut computation: Computation = circuit.into();
        for x in 0..127 {
            computation.set_u8(Party::A, x);
            computation.run()?;
            assert_eq!(computation.get_u8()?, x + y as u8);
        }
    }
    Ok(())
}
