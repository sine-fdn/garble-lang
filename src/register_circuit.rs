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
use crate::circuit::{GateIndex, MAX_GATES, Wire};

#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Reg(pub u32);

/// An instruction of a [`Circuit`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Inst {
    /// The register where the output must be stored.
    pub out: Reg,
    /// The [operation](`Op`) to execute.
    pub op: Op,
}

/// The operation of an [instruction](`Inst`).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Xor(pub Reg, pub Reg);

/// Computes the AND of its operands.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct And(pub Reg, pub Reg);

/// Computes the NOT of its operand.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Not(pub Reg);

/// Loads an input from a party into a register.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Input {
    /// Which party supplies this input.
    pub party: u32,
    /// Which input of the party should be stored.
    // TODO This limits each parties input to u32::MAX values, is this okay? (robinhundt 13.08.25)
    pub input: u32,
}

/// Errors occurring during the validation of the Circuit.
#[derive(Debug, PartialEq, Eq)]
pub enum CircuitError {
    /// The circuit does not specify any input instructions.
    EmptyInputs,
    /// The instruction at the specified position refers to a register greater than the max.
    InvalidInst(usize),
    /// The circuit does not specify any output registers.
    EmptyOutputs,
    /// The specified output register is invalid.
    InvalidOutput(Reg),
    /// The provided circuit has too many instructions to be processed.
    MaxCircuitSizeExceeded,
    /// The instruction at the specified position refers to a register before it is set.
    InvalidRegAccess(usize, Reg),
    /// The input instruction's output register is not equal to its position.
    InvalidInput(usize, Inst),
}

impl Circuit {
    /// Checks that the circuit only has valid instructions, has inputs andoutputs.
    pub fn validate(&self) -> Result<(), CircuitError> {
        let max_reg = Reg(self.max_reg_count.saturating_sub(1) as u32);
        if self.input_regs.iter().all(|i| *i == 0) {
            return Err(CircuitError::EmptyInputs);
        }

        if self.output_regs.is_empty() {
            return Err(CircuitError::EmptyOutputs);
        }
        for &o in self.output_regs.iter() {
            if o > max_reg {
                return Err(CircuitError::InvalidOutput(o));
            }
        }
        if self.insts.len() > MAX_GATES {
            return Err(CircuitError::MaxCircuitSizeExceeded);
        }

        let mut register_set = vec![false; self.max_reg_count];
        for (i, inst) in self.insts.iter().enumerate() {
            if inst.out > max_reg {
                return Err(CircuitError::InvalidInst(i));
            }
            match inst.op {
                Op::Input(_) => {
                    if i != inst.out.0 as usize {
                        return Err(CircuitError::InvalidInput(i, *inst));
                    }
                }
                Op::Xor(Xor(x, y)) | Op::And(And(x, y)) => {
                    if x > max_reg || y > max_reg {
                        return Err(CircuitError::InvalidInst(i));
                    }
                    if !register_set[x] {
                        return Err(CircuitError::InvalidRegAccess(i, x));
                    }
                    if !register_set[y] {
                        return Err(CircuitError::InvalidRegAccess(i, x));
                    }
                }
                Op::Not(Not(x)) => {
                    if x > max_reg {
                        return Err(CircuitError::InvalidInst(i));
                    }
                    if !register_set[x] {
                        return Err(CircuitError::InvalidRegAccess(i, x));
                    }
                }
            }
            register_set[inst.out] = true;
        }

        Ok(())
    }

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

// For some reason auto-ref auto-deref method dispatching works weirdly with
// `.into` calls for implied `Into` impls from `From` trait impls. If we
// just had `From<&SsaCircuit>` then some calls would require manual re-borrows.
impl From<SsaCircuit> for Circuit {
    fn from(circ: SsaCircuit) -> Self {
        let alloc = RegisterAllocator::new(&circ);
        alloc.convert_circuit()
    }
}

impl From<&SsaCircuit> for Circuit {
    fn from(circ: &SsaCircuit) -> Self {
        let alloc = RegisterAllocator::new(circ);
        alloc.convert_circuit()
    }
}

impl From<&mut SsaCircuit> for Circuit {
    fn from(circ: &mut SsaCircuit) -> Self {
        let alloc = RegisterAllocator::new(circ);
        alloc.convert_circuit()
    }
}

/// Used to convert an [`SsaCircuit`] into a register-based [`Circuit`].
struct RegisterAllocator<'c> {
    circ: &'c SsaCircuit,
    last_used: HashMap<GateIndex, GateIndex>,
    free_regs: Vec<Reg>,
    next_reg: u32,
    wire_map: HashMap<GateIndex, Reg>,
    insts: Vec<Inst>,
    and_ops: usize,
}

/// Compute the last use of a gates output value for each gate.
fn last_use_map(circ: &SsaCircuit) -> HashMap<GateIndex, GateIndex> {
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
    last_used
}

impl<'c> RegisterAllocator<'c> {
    fn new(circ: &'c SsaCircuit) -> Self {
        let last_used = last_use_map(circ);
        Self {
            circ,
            last_used,
            free_regs: vec![],
            next_reg: 0,
            wire_map: HashMap::new(),
            insts: Vec::with_capacity(circ.wires_len()),
            and_ops: 0,
        }
    }

    /// Convert the stored [`SsaCircuit`] into a register-based [`Circuit`] by
    /// allocating [`Reg`]s and converting wires into [`Inst`]ructions.
    fn convert_circuit(mut self) -> Circuit {
        // Iterate through circuit again and maintain list of free registers
        // If we use a value and the last use is the current gate idx
        // reuse the register for this instruction. If there are two whose
        // last use was this gate, store one in a list of available registers
        // If the gate was not the last use of a register, use the next highest
        // register idx (need to keep track of this).
        // We also need to maintain a map of gate idx -> register.

        // Initialize the instructions with the Input operations.
        // This assumes that the input wires in the original circuit have an increasing gate_id
        // which corresponds to their position in
        // `flatten(circ.input_gates.iter().map(|count| (0..count).to_vec()))`
        // Look at `Circuit::wires` for more context.
        for (party, inputs) in self.circ.input_gates.iter().enumerate() {
            for input in 0..*inputs {
                let op = Op::Input(Input {
                    party: party as u32,
                    input: input as u32,
                });
                let out = Reg(self.next_reg);
                self.next_reg += 1;
                self.insts.push(Inst { out, op });
            }
        }

        for (prev_gate_id, inp_ints) in self.insts.iter().enumerate() {
            self.wire_map.insert(prev_gate_id, inp_ints.out);
        }

        for (gate_id, w) in self.circ.wires().enumerate() {
            let inst = match w {
                Wire::Xor(a, b) => {
                    let op = Op::Xor(Xor(self.wire_map[&a], self.wire_map[&b]));
                    let out = self.find_out_reg(gate_id, a, Some(b));
                    Inst { op, out }
                }
                Wire::And(a, b) => {
                    let op = Op::And(And(self.wire_map[&a], self.wire_map[&b]));
                    let out = self.find_out_reg(gate_id, a, Some(b));
                    self.and_ops += 1;
                    Inst { op, out }
                }
                Wire::Not(a) => {
                    let op = Op::Not(Not(self.wire_map[&a]));
                    let out = self.find_out_reg(gate_id, a, None);
                    Inst { op, out }
                }
                Wire::Input(_) => {
                    // already handled above separately. We still use the wires iterator
                    // for the correct gate_ids
                    continue;
                }
            };
            self.wire_map.insert(gate_id, inst.out);
            self.insts.push(inst);
        }

        let output_regs = self
            .circ
            .output_gates
            .iter()
            .map(|gate_id| self.wire_map[gate_id])
            .collect();

        Circuit {
            input_regs: self.circ.input_gates.clone(),
            insts: self.insts,
            max_reg_count: self.next_reg as usize,
            output_regs,
            and_ops: self.and_ops,
        }
    }

    /// Finds a free output register or allocates a new one and updates the wire_map.
    /// If the current gate is the last use of one its inputs, we immediately reuse
    /// the register.
    fn find_out_reg(&mut self, gate_id: GateIndex, a: GateIndex, b: Option<GateIndex>) -> Reg {
        let mut reuse_reg = None;
        if let Some(&last_use) = self.last_used.get(&a) {
            if last_use == gate_id {
                let Some(reg) = self.wire_map.remove(&a) else {
                    unreachable!(
                        "Compile Error: gate_id: {gate_id} a: {a}, wire_map: {:?}",
                        self.wire_map
                    )
                };
                reuse_reg = Some(reg);
            }
        }
        if let Some(b) = b {
            if let Some(&last_use) = self.last_used.get(&b) {
                if last_use == gate_id {
                    // This might be None if a == b, as we already removed a previously
                    if let Some(reg) = self.wire_map.remove(&b) {
                        if reuse_reg.is_some() {
                            self.free_regs.push(reg);
                        } else {
                            reuse_reg = Some(reg);
                        }
                    }
                }
            }
        }

        if let Some(reg) = reuse_reg {
            reg
        } else if let Some(reg) = self.free_regs.pop() {
            reg
        } else {
            self.next_reg += 1;
            Reg(self.next_reg - 1)
        }
    }
}

// These impls make working with Regs nicer as they allow us to index Vecs and slices.

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

/// There are some basic unit tests for the Circuit here.
/// We also comprehensively test both circuit reprs in the `tests/compile.rs` integration tests.
#[cfg(test)]
mod tests {
    use crate::circuit::Gate;

    use super::*;

    #[test]
    fn compute_last_uses() {
        let c = SsaCircuit {
            input_gates: vec![1, 2],
            gates: vec![Gate::Xor(0, 1), Gate::Xor(0, 2), Gate::Xor(3, 4)],
            output_gates: vec![5],
        };
        let last_uses = last_use_map(&c);
        let expected =
            HashMap::from_iter([(0, 4), (1, 3), (2, 4), (3, 5), (4, 5), (5, usize::MAX)]);
        assert_eq!(expected, last_uses);
    }

    #[test]
    fn convert_ssa_to_register() {
        let c = SsaCircuit {
            input_gates: vec![1, 2],
            gates: vec![
                Gate::Xor(0, 1),
                Gate::And(0, 2),
                Gate::Xor(3, 4),
                Gate::And(4, 5),
            ],
            output_gates: vec![5, 6],
        };

        #[rustfmt::skip]
        let expected = Circuit {
            input_regs: vec![1, 2],
            insts: vec![
                Inst { out: Reg(0), op: Op::Input(Input { party: 0, input: 0 }) },
                Inst { out: Reg(1), op: Op::Input(Input { party: 1, input: 0 }) },
                Inst { out: Reg(2), op: Op::Input(Input { party: 1, input: 1 }) },
                Inst { out: Reg(1), op: Op::Xor(Xor(Reg(0), Reg(1))) },
                Inst { out: Reg(0), op: Op::And(And(Reg(0), Reg(2))) },
                Inst { out: Reg(1), op: Op::Xor(Xor(Reg(1), Reg(0))) },
                Inst { out: Reg(0), op: Op::And(And(Reg(0), Reg(1))) },
            ],
            max_reg_count: 3,
            output_regs: vec![Reg(1), Reg(0)],
            and_ops: 2,
        };
        assert_eq!(expected, c.into());
    }
}
