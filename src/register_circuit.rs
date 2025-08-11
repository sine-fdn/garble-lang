//! A register-based circuit representation.
//!
//! Contrary to the regular [circuit representation](`SsaCircuit`), the [`register_circuit::Circuit`](`Circuit`)
//! contains [Instructions](`Inst`) which have input and output [registers](`Reg`). These registers might
//! be written to multiple times.

use std::{
    collections::HashMap,
    ops::{Index, IndexMut},
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub use crate::circuit::Circuit as SsaCircuit;
use crate::circuit::{GateIndex, Wire};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
/// A circuit representation with [instructions][`Inst`] that operate on
/// [registers](`Reg`).
pub struct Circuit {
    /// Number of inputs per party.
    pub input_regs: Vec<usize>,
    /// Topologically sorted list of instructions.
    pub insts: Vec<Inst>,
    /// Maximum number of registers needed to execute this circuit.
    pub max_reg_count: usize,
    /// Registers that hold the output values at the end of the evaluation.
    pub output_regs: Vec<Reg>,
    /// Number of `AND` operations.
    pub and_ops: usize,
}

impl Circuit {
    /// Total number of inputs for all parties.
    pub fn total_inputs(&self) -> usize {
        self.input_regs.iter().sum()
    }
}

/// A register identifier.
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Reg(pub u32);

/// An instruction of a [`Circuit`].
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Inst {
    /// The register where the output must be stored.
    pub out: Reg,
    /// The [operation](`Op`) to execute.
    pub op: Op,
}

/// The operation of an [instruction](`Inst`).
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Op {
    /// Computes the XOR of its operands.
    Xor(Xor),
    /// Computes the AND of its operands.
    And(And),
    /// Computes the NOT of its operand.
    Not(Not),
    /// Loads an input from a party into a register.
    Input(Input), // TODO maybe have an output op instead of storing output regs in circuit?
                  // For Op, we'd need to emit them in the right order
}

/// Computes the XOR of its operands.
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Xor(pub Reg, pub Reg);

/// Computes the AND of its operands.
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct And(pub Reg, pub Reg);

/// Computes the NOT of its operand.
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Not(pub Reg);

/// Loads an input from a party into a register.
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Input {
    /// Which party supplies this input.
    pub party: u32,
    /// Which input of the party should be stored.
    // TODO This limits each parties input to u32::MAX values, is this okay? (robinhundt 13.08.25)
    pub input: u32,
}

impl From<SsaCircuit> for Circuit {
    fn from(circ: SsaCircuit) -> Self {
        // Convert the SsaCircuit (the previous normal Circuit) into a circuit
        // of instructions writing to registers
        //
        // First: build a map of last uses of wire in the SsaCircuit
        // E.g. if value at gate_index 2 is used the last time as the input
        // for gate 3, store: 2 -> 3
        let mut last_used = HashMap::with_capacity(circ.wires_len());

        for (gate_id, w) in circ.wires().enumerate() {
            match w {
                Wire::Xor(a, b) | Wire::And(a, b) => {
                    last_used.insert(a, gate_id);
                    last_used.insert(b, gate_id);
                }
                Wire::Not(a) => {
                    last_used.insert(a, gate_id);
                }
                Wire::Input(_) => {
                    // Inputs use no other wires
                }
            }
        }
        // Output gates output register can never be reused, so
        // we set the last_use to usize::MAX
        for &gate_id in &circ.output_gates {
            last_used.insert(gate_id, usize::MAX);
        }

        // Iterate through circuit again and maintain list of free registers
        // If we use a value and the last use is the current gate idx
        // reuse the register for this instruction. If there are two whose
        // last use was this gate, store one in a list of available registers
        // If the gate was not the last use of a register, use the next highest
        // register idx (need to keep track of this)
        // We also need to maintain a map of gate idx -> register

        let mut free_regs = vec![];
        let mut next_reg = 0;
        let mut wire_map = HashMap::with_capacity(circ.wires_len());
        let mut insts = Vec::with_capacity(circ.gates.len());
        let mut and_ops = 0;

        // Initiliaze the instructions with the Input operations.
        // This assumes that the input wires in the original circuit have an increasing gate_id
        // which corresponds to their position in
        // `flatten(circ.input_gates.iter().map(|count| (0..count).to_vec()))`
        // Look at `Circuit::wires` for more context.
        for (party, inputs) in circ.input_gates.iter().enumerate() {
            for input in 0..*inputs {
                let op = Op::Input(Input {
                    party: party as u32,
                    input: input as u32,
                });
                let out = Reg(next_reg);
                next_reg += 1;
                insts.push(Inst { out, op });
            }
        }

        for (prev_gate_id, inp_ints) in insts.iter().enumerate() {
            wire_map.insert(prev_gate_id, inp_ints.out);
        }

        // Finds a free output register or allocates a new one and updates the wire_map.
        // If the current gate is the last use of one its inputs, we immediately reuse
        // the register.
        let mut find_out_reg = |gate_id: GateIndex,
                                wire_map: &mut HashMap<usize, Reg>,
                                a: usize,
                                b: Option<usize>|
         -> Reg {
            let mut reuse_reg = None;
            if let Some(&last_use) = last_used.get(&a) {
                if last_use == gate_id {
                    let Some(reg) = wire_map.remove(&a) else {
                        unreachable!(
                            "Compile Error: gate_id: {gate_id} a: {a}, wire_map: {wire_map:?}"
                        )
                    };
                    reuse_reg = Some(reg);
                }
            }
            if let Some(b) = b {
                if let Some(&last_use) = last_used.get(&b) {
                    if last_use == gate_id {
                        // This might be None if a == b, as we already removed a previously
                        if let Some(reg) = wire_map.remove(&b) {
                            if reuse_reg.is_some() {
                                free_regs.push(reg);
                            } else {
                                reuse_reg = Some(reg);
                            }
                        }
                    }
                }
            }

            if let Some(reg) = reuse_reg {
                reg
            } else if let Some(reg) = free_regs.pop() {
                reg
            } else {
                next_reg += 1;
                Reg(next_reg - 1)
            }
        };

        for (gate_id, w) in circ.wires().enumerate() {
            let inst = match w {
                Wire::Xor(a, b) => {
                    let op = Op::Xor(Xor(wire_map[&a], wire_map[&b]));
                    let out = find_out_reg(gate_id, &mut wire_map, a, Some(b));
                    Inst { op, out }
                }
                Wire::And(a, b) => {
                    let op = Op::And(And(wire_map[&a], wire_map[&b]));
                    let out = find_out_reg(gate_id, &mut wire_map, a, Some(b));
                    and_ops += 1;
                    Inst { op, out }
                }
                Wire::Not(a) => {
                    let op = Op::Not(Not(wire_map[&a]));
                    let out = find_out_reg(gate_id, &mut wire_map, a, None);
                    Inst { op, out }
                }
                Wire::Input(_) => {
                    // already handled above separately. We still use the wires iterator
                    // for the correct gate_ids
                    continue;
                }
            };
            wire_map.insert(gate_id, inst.out);
            insts.push(inst);
        }

        let output_regs = circ
            .output_gates
            .iter()
            .map(|gate_id| wire_map[gate_id])
            .collect();

        Circuit {
            input_regs: circ.input_gates,
            insts,
            max_reg_count: next_reg as usize,
            output_regs,
            and_ops,
        }
    }
}

impl Circuit {
    /// Evaluates the circuit with the specified inputs (with one `Vec<bool>` per party).
    ///
    /// Assumes that the inputs have been previously type-checked and **panics** if the number of
    /// parties or the bits of a particular party do not match the circuit.
    pub fn eval(&self, inputs: &[Vec<bool>]) -> Vec<bool> {
        if inputs.len() != self.input_regs.len() {
            panic!(
                "Circuit was built for {} parties, but found {} inputs",
                self.input_regs.len(),
                inputs.len()
            );
        }
        for (p, &input_regs) in self.input_regs.iter().enumerate() {
            if input_regs != inputs[p].len() {
                panic!(
                    "Expected {} input bits for party {}, but found {}",
                    input_regs,
                    p,
                    inputs[p].len()
                );
            }
        }

        let mut regs = vec![false; self.max_reg_count];

        for inst in &self.insts {
            regs[inst.out] = match inst.op {
                Op::Xor(Xor(a, b)) => regs[a] ^ regs[b],
                Op::And(And(a, b)) => regs[a] & regs[b],
                Op::Not(Not(a)) => !regs[a],
                Op::Input(Input { party, input }) => inputs[party as usize][input as usize],
            };
        }
        self.output_regs.iter().map(|r| regs[*r]).collect()
    }
}

impl<T> Index<Reg> for Vec<T> {
    type Output = T;

    fn index(&self, index: Reg) -> &Self::Output {
        &self[index.0 as usize]
    }
}

impl<T> Index<Reg> for [T] {
    type Output = T;

    fn index(&self, index: Reg) -> &Self::Output {
        &self[index.0 as usize]
    }
}

impl<T> IndexMut<Reg> for Vec<T> {
    fn index_mut(&mut self, index: Reg) -> &mut Self::Output {
        &mut self[index.0 as usize]
    }
}

impl<T> IndexMut<Reg> for [T] {
    fn index_mut(&mut self, index: Reg) -> &mut Self::Output {
        &mut self[index.0 as usize]
    }
}
