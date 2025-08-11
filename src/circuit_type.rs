//! Unifies normal SSA-based [`Circuit`](circuit::Circuit) and [register-based](`register_circuit::Circuit`) one.
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{circuit, register_circuit};

/// Either [`circuit::Circuit`] or [`register_circuit::Circuit`].
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[allow(missing_docs)]
pub enum CircuitType {
    Ssa(circuit::Circuit),
    Register(register_circuit::Circuit),
}

impl CircuitType {
    /// Unwraps a [`circuit::Circuit`], panicks if a [`register_circuit::Circuit`] is stored.
    pub fn unwrap_ssa(self) -> circuit::Circuit {
        match self {
            CircuitType::Ssa(circuit) => circuit,
            CircuitType::Register(_) => {
                panic!("CircuitType contains Register variant but Ssa was expected")
            }
        }
    }

    /// Unwraps a reference to a[`circuit::Circuit`], panicks if a [`register_circuit::Circuit`] is stored.
    pub fn unwrap_ssa_ref(&self) -> &circuit::Circuit {
        match self {
            CircuitType::Ssa(circuit) => circuit,
            CircuitType::Register(_) => {
                panic!("CircuitType contains Register variant but Ssa was expected")
            }
        }
    }

    /// Unwraps a [`register_circuit::Circuit`], panicks if a [`circuit::Circuit`] is stored.
    pub fn unwrap_register(self) -> register_circuit::Circuit {
        match self {
            CircuitType::Ssa(_) => {
                panic!("CircuitType contains Ssa variant but Register was expected")
            }
            CircuitType::Register(circuit) => circuit,
        }
    }

    /// Unwraps a ref to a [`register_circuit::Circuit`], panicks if a [`circuit::Circuit`] is stored.
    pub fn unwrap_register_ref(&self) -> &register_circuit::Circuit {
        match self {
            CircuitType::Ssa(_) => {
                panic!("CircuitType contains Ssa variant but Register was expected")
            }
            CircuitType::Register(circuit) => circuit,
        }
    }

    /// Number of parties this circuit is compiled for.
    pub fn parties(&self) -> usize {
        match self {
            CircuitType::Ssa(circuit) => circuit.input_gates.len(),
            CircuitType::Register(circuit) => circuit.input_regs.len(),
        }
    }

    /// Number of inputs for each party in order.
    pub fn input_lengths(&self) -> impl Iterator<Item = usize> + use<'_> {
        match self {
            CircuitType::Ssa(circuit) => circuit.input_gates.iter().copied(),
            CircuitType::Register(circuit) => circuit.input_regs.iter().copied(),
        }
    }

    /// Number of operations (gates or instructions) without inputs.
    pub fn ops(&self) -> usize {
        match self {
            CircuitType::Ssa(circuit) => circuit.gates.len(),
            CircuitType::Register(circuit) => circuit.insts.len() - circuit.total_inputs(),
        }
    }

    /// Number of AND operations.
    pub fn ands(&self) -> usize {
        match self {
            CircuitType::Ssa(circuit) => circuit.and_gates(),
            CircuitType::Register(circuit) => circuit.and_ops,
        }
    }

    /// Convert [`CircuitType::Ssa`] to [`CircuitType::Register`].
    ///
    /// Does nothing if is already [`CircuitType::Register`].
    pub fn to_register(&mut self) {
        match self {
            CircuitType::Ssa(circuit) => *self = CircuitType::Register(circuit.into()),
            CircuitType::Register(_) => (),
        }
    }

    /// Evaluates the circuit with the specified inputs (with one `Vec<bool>` per party).
    ///
    /// Assumes that the inputs have been previously type-checked and **panics** if the number of
    /// parties or the bits of a particular party do not match the circuit.
    pub fn eval(&self, inputs: &[Vec<bool>]) -> Vec<bool> {
        match self {
            CircuitType::Ssa(circuit) => circuit.eval(inputs),
            CircuitType::Register(circuit) => circuit.eval(inputs),
        }
    }
}
