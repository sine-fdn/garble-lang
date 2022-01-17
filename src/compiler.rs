use std::collections::{HashMap, HashSet};

use crate::{
    ast::{MetaInfo, Op, ParamDef, Party, Type},
    circuit::{Circuit, Gate, GateIndex},
    typed_ast::{Expr, ExprEnum, MainDef, Program},
};

impl Program {
    pub fn compile(&self) -> Circuit {
        // TODO: compile non-main fn defs
        let mut bindings = HashMap::new();
        let mut gates = vec![];
        let mut wire = 2;
        for (party, ParamDef(identifier, ty)) in self.main.params.iter() {
            let type_size = match ty {
                Type::Bool => 1,
                Type::U8 => 8,
            };
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
            ExprEnum::NumU8(n) => {
                let mut bits = Vec::with_capacity(8);
                u8_to_bits(*n, &mut bits);
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::Identifier(s) => env.get(s),
            ExprEnum::Op(op, x, y) => {
                let x = x.compile(env, gates);
                let y = y.compile(env, gates);
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
                            Type::U8 => {
                                let mut carry = 0;
                                let mut sum = vec![0; 8];
                                // sequence of full adders:
                                for i in 0..8 {
                                    let i = 7 - i;
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
    OutputDoesNotHaveType(Type),
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
            Err(ComputeError::OutputDoesNotHaveType(Type::Bool))
        }
    }

    pub fn set_u8(&mut self, p: Party, n: u8) {
        let inputs = self.get_input(p);
        u8_to_bits(n, inputs);
    }

    pub fn get_u8(&self) -> Result<u8, ComputeError> {
        let output = self.get_output()?;
        if output.len() == 8 {
            let mut n = 0;
            for i in 0..8 {
                n += (output[i] as u8) << (7 - i);
            }
            Ok(n)
        } else {
            Err(ComputeError::OutputDoesNotHaveType(Type::U8))
        }
    }
}

fn u8_to_bits(n: u8, bits: &mut Vec<bool>) {
    for i in 0..8 {
        bits.push((n >> (7 - i) & 1) == 1);
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
                        Box::new(Expr(ExprEnum::NumU8(y), Type::U8, MetaInfo {})),
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
            assert_eq!(computation.get_u8()?, x + y);
        }
    }
    Ok(())
}
