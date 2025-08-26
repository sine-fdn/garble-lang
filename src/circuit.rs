//! The [`Circuit`] representation used by the compiler.

use crate::{compile::wires_as_unsigned, env::Env, token::MetaInfo};
use std::{
    collections::{HashMap, HashSet},
    mem,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

// This module currently implements a few basic kinds of circuit optimizations:
//
// 1. Constant evaluation (e.g. x ^ 0 == x; x & 1 == x; x & 0 == 0)
// 2. Sub-expression sharing (wires are re-used if a gate with the same type and inputs exists)
// 3. Pruning of useless gates (gates that are not part of the output nor used by other gates)

const PRINT_OPTIMIZATION_RATIO: bool = false;
const MAX_GATES: usize = u32::MAX as usize;

/// Data type to uniquely identify gates.
pub type GateIndex = usize;

/// Description of a gate executed under MPC.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Gate {
    /// A logical XOR gate attached to the two specified input wires.
    Xor(GateIndex, GateIndex),
    /// A logical AND gate attached to the two specified input wires.
    And(GateIndex, GateIndex),
    /// A logical NOT gate attached to the specified input wire.
    Not(GateIndex),
}

/// Representation of a circuit evaluated by an MPC engine.
///
/// Each circuit consists of 3 parts:
///
///   1. `input_gates`, specifying how many input bits each party must provide
///   2. `gates`, XOR/AND/NOT intermediate gates (with input gates or intermediate gates as inputs)
///   3. `output_gates`, specifying which gates should be exposed as outputs (and in which order)
///
/// Conceptually, a circuit is a sequence of input or intermediate (XOR/AND/NOT) gates, with all
/// input gates at the beginning of the sequence, followed by all intermediate gates. The index of a
/// gate in the sequence determines its "wire". For example, in a circuit with two input gates (1
/// bit for party A, 1 bit for party B), followed by three intermediate gates (an XOR of the two
/// input gates, an AND of the two input gates, and an XOR of these two intermediate XOR/AND gates),
/// the input gates would be the wires 0 and 1, the XOR of these two input gates would be specified
/// as `Gate::Xor(0, 1)` and have the wire 2, the AND of the two input gates would be specified as
/// `Gate::And(0, 1)` and have the wire 3, and the XOR of the two intermediate gates would be
/// specified as `Gate::Xor(2, 3)` and have the wire 4:
///
/// ```text
/// Input A (Wire 0) ----+----------+
///                      |          |
/// Input B (Wire 1) ----|-----+----|-----+
///                      |     |    |     |
///                      +-XOR-+    |     |
///         (Wire 2) =====> |       |     |
///                         |       +-AND-+
///         (Wire 3) =======|========> |
///                         +---XOR----+
///         (Wire 4) ==========> |
/// ```
///
/// The input gates of different parties cannot be interleaved: Each party must supply all of their
/// inputs before the next party's inputs can start. Consequently, a circuit with 16 input bits from
/// party A, 8 input bits from party B and 1 input bit from party C would be specified as an
/// `input_gates` field of `vec![16, 8, 1]`.
///
/// At least 1 input bit must be specified, not just because a circuit without inputs would not be
/// very useful, but also because the first two intermediate gates of every circuit are constant
/// true and constant false, specified as `Gate::Xor(0, 0)` with wire `n` and `Gate::Not(n)` (and
/// thus depend on the first input bit for their specifications).
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Circuit {
    /// The different parties, with `usize` at index `i` as the number of input bits for party `i`.
    pub input_gates: Vec<usize>,
    /// The non-input intermediary gates.
    pub gates: Vec<Gate>,
    /// The indices of the gates in [`Circuit::gates`] that produce output bits.
    pub output_gates: Vec<GateIndex>,
}

/// An input wire or a gate operating on them.
pub enum Wire {
    /// An input wire, with its value coming directly from one of the parties.
    Input(GateIndex),
    /// A logical XOR gate attached to the two specified input wires.
    Xor(GateIndex, GateIndex),
    /// A logical AND gate attached to the two specified input wires.
    And(GateIndex, GateIndex),
    /// A logical NOT gate attached to the specified input wire.
    Not(GateIndex),
}

/// Errors occurring during the validation or the execution of the MPC protocol.
#[derive(Debug, PartialEq, Eq)]
pub enum CircuitError {
    /// The gate with the specified wire contains invalid gate connections.
    InvalidGate(usize),
    /// The specified output gate does not exist in the circuit.
    InvalidOutput(usize),
    /// The circuit does not specify any input gates.
    EmptyInputs,
    /// The circuit does not specify any output gates.
    EmptyOutputs,
    /// The provided circuit has too many gates to be processed.
    MaxCircuitSizeExceeded,
    /// The provided index does not correspond to any party.
    PartyIndexOutOfBounds,
}

impl Circuit {
    /// Returns all the wires (inputs + gates) in the circuit, in ascending order.
    pub fn wires(&self) -> impl Iterator<Item = Wire> + use<'_> {
        let input_gates = self
            .input_gates
            .iter()
            .enumerate()
            .flat_map(|(party, inputs)| (0..*inputs).map(move |_| Wire::Input(party)));

        let gates = self.gates.iter().map(|gate| match gate {
            Gate::Xor(x, y) => Wire::Xor(*x, *y),
            Gate::And(x, y) => Wire::And(*x, *y),
            Gate::Not(x) => Wire::Not(*x),
        });
        input_gates.chain(gates)
    }

    /// Returns the number of wires in this circuit.
    ///
    /// Equal to the number of items returnes by the [`Circuit::wires`] iterator.
    pub fn wires_len(&self) -> usize {
        let mut len = self.input_gates.iter().sum();
        len += self.gates.len();
        len
    }

    /// Returns the number of AND gates in the circuit.
    pub fn and_gates(&self) -> usize {
        self.gates
            .iter()
            .filter(|g| matches!(g, Gate::And(_, _)))
            .count()
    }

    /// Checks that the circuit only uses valid wires, includes no cycles, has outputs, etc.
    pub fn validate(&self) -> Result<(), CircuitError> {
        let wires = self.wires();
        if self.input_gates.iter().all(|i| *i == 0) {
            return Err(CircuitError::EmptyInputs);
        }
        for (i, g) in wires.enumerate() {
            match g {
                Wire::Input(_) => {}
                Wire::Xor(x, y) | Wire::And(x, y) => {
                    if x >= i || y >= i {
                        return Err(CircuitError::InvalidGate(i));
                    }
                }
                Wire::Not(x) => {
                    if x >= i {
                        return Err(CircuitError::InvalidGate(i));
                    }
                }
            }
        }
        if self.output_gates.is_empty() {
            return Err(CircuitError::EmptyOutputs);
        }
        for &o in self.output_gates.iter() {
            if o >= self.wires_len() {
                return Err(CircuitError::InvalidOutput(o));
            }
        }
        if self.wires_len() + self.input_gates.iter().sum::<usize>() > MAX_GATES {
            return Err(CircuitError::MaxCircuitSizeExceeded);
        }
        Ok(())
    }

    /// Evaluates the circuit with the specified inputs (with one `Vec<bool>` per party).
    ///
    /// Assumes that the inputs have been previously type-checked and **panics** if the number of
    /// parties or the bits of a particular party do not match the circuit.
    pub fn eval(&self, inputs: &[Vec<bool>]) -> Vec<bool> {
        let mut input_len = 0;
        for p in self.input_gates.iter() {
            input_len += p;
        }
        let mut output = vec![None; input_len + self.gates.len()];
        let inputs: Vec<_> = inputs.iter().map(|inputs| inputs.iter()).collect();
        let mut i = 0;
        if self.input_gates.len() != inputs.len() {
            panic!(
                "Circuit was built for {} parties, but found {} inputs",
                self.input_gates.len(),
                inputs.len()
            );
        }
        for (p, &input_gates) in self.input_gates.iter().enumerate() {
            if input_gates != inputs[p].len() {
                panic!(
                    "Expected {} input bits for party {}, but found {}",
                    input_gates,
                    p,
                    inputs[p].len()
                );
            }
            for bit in inputs[p].as_slice() {
                output[i] = Some(*bit);
                i += 1;
            }
        }
        for (w, gate) in self.gates.iter().enumerate() {
            let w = w + i;
            let output_bit = match gate {
                Gate::Xor(x, y) => output[*x].unwrap() ^ output[*y].unwrap(),
                Gate::And(x, y) => output[*x].unwrap() & output[*y].unwrap(),
                Gate::Not(x) => !output[*x].unwrap(),
            };
            output[w] = Some(output_bit);
        }

        let mut output_packed: Vec<bool> = Vec::with_capacity(self.output_gates.len());
        for output_gate in &self.output_gates {
            output_packed.push(output[*output_gate].unwrap());
        }
        output_packed
    }

    /// Returns the number of gates in the circuit as a formatted string.
    ///
    /// E.g. "79k gates (XOR: 44k, NOT: 13k, AND: 21k)"
    pub fn report_gates(&self) -> String {
        let mut num_xor = 0;
        let mut num_and = 0;
        let mut num_not = 0;
        for gate in self.gates.iter() {
            match gate {
                Gate::Xor(_, _) => num_xor += 1,
                Gate::And(_, _) => num_and += 1,
                Gate::Not(_) => num_not += 1,
            }
        }
        num_xor /= 1000;
        num_and /= 1000;
        num_not /= 1000;
        format!(
            "{}k gates (XOR: {num_xor}k, NOT: {num_not}k, AND: {num_and}k)",
            self.gates.len() / 1000
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BuilderGate {
    Xor(GateIndex, GateIndex),
    And(GateIndex, GateIndex),
}

#[derive(Debug, Clone)]
pub(crate) struct CircuitBuilder {
    shift: usize,
    input_gates: Vec<usize>,
    gates: Vec<BuilderGate>,
    used: HashSet<GateIndex>,
    cache: HashMap<BuilderGate, GateIndex>,
    negated: HashMap<GateIndex, GateIndex>,
    gates_optimized: usize,
    gate_counter: usize,
    panic_gates: CachedPanicResult,
    consts: HashMap<String, usize>,
}

pub(crate) const USIZE_BITS: usize = 32;
/// The number of bits needed to represent a panic result.
pub const PANIC_RESULT_SIZE_IN_BITS: usize = 1 + 5 * USIZE_BITS;

/// A collection of wires that carry information about whether and where a panic occurred.
#[derive(Debug, Clone)]
pub struct PanicResult {
    /// A Boolean wire indicating whether a panic has occurred.
    pub has_panicked: GateIndex,
    /// The (encoded) reason why the panic occurred (overflow, div-by-zero, etc).
    pub panic_type: [GateIndex; USIZE_BITS],
    /// The (encoded) first line in the source code where the panic occurred.
    pub start_line: [GateIndex; USIZE_BITS],
    /// The (encoded) first column of the first line in the source code where the panic occurred.
    pub start_column: [GateIndex; USIZE_BITS],
    /// The (encoded) last line in the source code where the panic occurred.
    pub end_line: [GateIndex; USIZE_BITS],
    /// The (encoded) last column of the last line in the source code where the panic occurred.
    pub end_column: [GateIndex; USIZE_BITS],
}

#[derive(Debug, Clone)]
pub(crate) struct CachedPanicResult {
    result: PanicResult,
    cache: HashMap<usize, PanicResult>,
}

impl PanicResult {
    /// Returns a `PanicResult` indicating that no panic has occurred.
    pub fn ok() -> Self {
        Self {
            has_panicked: 0,
            panic_type: PanicReason::Overflow.as_bits(),
            start_line: [0; USIZE_BITS],
            start_column: [0; USIZE_BITS],
            end_line: [0; USIZE_BITS],
            end_column: [0; USIZE_BITS],
        }
    }
}

/// A decoded panic, indicating why and where a panic occurred.
#[derive(Debug, Clone)]
pub struct EvalPanic {
    /// The reason why the panic occurred.
    pub reason: PanicReason,
    /// The location in the source code where the panic occurred.
    pub panicked_at: MetaInfo,
}

impl EvalPanic {
    pub(crate) fn parse(bits: &[bool]) -> Result<&[bool], EvalPanic> {
        let has_panicked = bits[0];
        let panic_type: [bool; USIZE_BITS] = bits[1..USIZE_BITS + 1].try_into().unwrap();
        let start_line: [bool; USIZE_BITS] = bits[USIZE_BITS + 1..(2 * USIZE_BITS) + 1]
            .try_into()
            .unwrap();
        let start_column: [bool; USIZE_BITS] = bits[(2 * USIZE_BITS) + 1..(3 * USIZE_BITS) + 1]
            .try_into()
            .unwrap();
        let end_line: [bool; USIZE_BITS] = bits[(3 * USIZE_BITS) + 1..(4 * USIZE_BITS) + 1]
            .try_into()
            .unwrap();
        let end_column: [bool; USIZE_BITS] = bits[(4 * USIZE_BITS) + 1..(5 * USIZE_BITS) + 1]
            .try_into()
            .unwrap();
        let reason = PanicReason::from_num(wires_as_unsigned(&panic_type) as usize);
        if has_panicked {
            Err(EvalPanic {
                reason,
                panicked_at: MetaInfo {
                    start: (
                        wires_as_unsigned(&start_line) as usize,
                        wires_as_unsigned(&start_column) as usize,
                    ),
                    end: (
                        wires_as_unsigned(&end_line) as usize,
                        wires_as_unsigned(&end_column) as usize,
                    ),
                },
            })
        } else {
            Ok(&bits[5 * USIZE_BITS + 1..])
        }
    }
}

/// The reason why a panic occurred.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PanicReason {
    /// Arithmetic overflow.
    Overflow,
    /// Division by zero.
    DivByZero,
    /// Array out of bounds access.
    OutOfBounds,
}

impl std::fmt::Display for PanicReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            PanicReason::Overflow => "Overflow",
            PanicReason::DivByZero => "Division By Zero",
            PanicReason::OutOfBounds => "Array Access Out Of Bounds",
        })
    }
}

impl PanicReason {
    fn from_num(n: usize) -> Self {
        match n {
            1 => PanicReason::Overflow,
            2 => PanicReason::DivByZero,
            3 => PanicReason::OutOfBounds,
            r => panic!("Invalid panic reason: {r}"),
        }
    }

    fn as_bits(&self) -> [GateIndex; USIZE_BITS] {
        let n = match self {
            PanicReason::Overflow => 1,
            PanicReason::DivByZero => 2,
            PanicReason::OutOfBounds => 3,
        };
        unsigned_as_usize_bits(n)
    }
}

impl CircuitBuilder {
    pub fn new(input_gates: Vec<usize>, consts: HashMap<String, usize>) -> Self {
        let mut gate_counter = 2; // for const true and false
        for input_gates_of_party in input_gates.iter() {
            gate_counter += input_gates_of_party;
        }
        Self {
            shift: gate_counter,
            input_gates,
            gates: vec![],
            used: HashSet::new(),
            cache: HashMap::new(),
            negated: HashMap::new(),
            gates_optimized: 0,
            gate_counter,
            panic_gates: CachedPanicResult {
                result: PanicResult::ok(),
                cache: HashMap::new(),
            },
            consts,
        }
    }

    pub fn const_sizes(&self) -> &HashMap<String, usize> {
        &self.consts
    }

    fn get_cached(&self, gate: &BuilderGate) -> Option<&usize> {
        match self.cache.get(gate) {
            Some(wire) => Some(wire),
            None => match gate {
                BuilderGate::Xor(x, y) => self.cache.get(&BuilderGate::Xor(*y, *x)),
                BuilderGate::And(x, y) => self.cache.get(&BuilderGate::And(*y, *x)),
            },
        }
    }

    // Pruning of useless gates (gates that are not part of the output nor used by other gates):
    fn remove_unused_gates(&mut self, output_gates: Vec<GateIndex>) -> Vec<GateIndex> {
        // To find all unused gates, we start at the output gates and recursively mark all their
        // inputs (and their inputs, etc.) as used:
        let shift = self.shift;
        let mut output_gate_stack = output_gates.clone();
        output_gate_stack.push(self.panic_gates.result.has_panicked);
        output_gate_stack.extend(self.panic_gates.result.panic_type.iter());
        output_gate_stack.extend(self.panic_gates.result.start_line.iter());
        output_gate_stack.extend(self.panic_gates.result.start_column.iter());
        output_gate_stack.extend(self.panic_gates.result.end_line.iter());
        output_gate_stack.extend(self.panic_gates.result.end_column.iter());
        let mut used_gates = vec![false; self.gates.len()];
        while let Some(gate_index) = output_gate_stack.pop() {
            if gate_index >= shift {
                let shifted_index = gate_index - shift;
                used_gates[shifted_index] = true;
                let (x, y) = match self.gates[shifted_index] {
                    BuilderGate::Xor(x, y) => (x, y),
                    BuilderGate::And(x, y) => (x, y),
                };
                if x >= shift && !used_gates[x - shift] {
                    output_gate_stack.push(x);
                }
                if y >= shift && !used_gates[y - shift] {
                    output_gate_stack.push(y);
                }
            }
        }
        let mut unused_gates = 0;
        let mut unused_before_gate = vec![0; self.gates.len()];
        for (w, used) in used_gates.iter().enumerate() {
            if !used {
                unused_gates += 1;
            }
            unused_before_gate[w] = unused_gates;
        }
        // Now that we know which gates are useless, iterate through the circuit and shift the
        // indices of the useful gates to reuse the freed space:
        let shift_gate_index_if_necessary = |index: usize| {
            if index > shift {
                index - unused_before_gate[index - shift]
            } else {
                index
            }
        };
        for gate in self.gates.iter_mut() {
            let (x, y) = match gate {
                BuilderGate::Xor(x, y) => (x, y),
                BuilderGate::And(x, y) => (x, y),
            };
            *x = shift_gate_index_if_necessary(*x);
            *y = shift_gate_index_if_necessary(*y);
        }
        self.panic_gates.result.has_panicked =
            shift_gate_index_if_necessary(self.panic_gates.result.has_panicked);
        for w in self.panic_gates.result.panic_type.iter_mut() {
            *w = shift_gate_index_if_necessary(*w);
        }
        for w in self.panic_gates.result.start_line.iter_mut() {
            *w = shift_gate_index_if_necessary(*w);
        }
        for w in self.panic_gates.result.start_column.iter_mut() {
            *w = shift_gate_index_if_necessary(*w);
        }
        for w in self.panic_gates.result.end_line.iter_mut() {
            *w = shift_gate_index_if_necessary(*w);
        }
        for w in self.panic_gates.result.end_column.iter_mut() {
            *w = shift_gate_index_if_necessary(*w);
        }
        let mut without_unused_gates = Vec::with_capacity(self.gates.len() - unused_gates);
        for (w, &used) in used_gates.iter().enumerate() {
            if used {
                without_unused_gates.push(self.gates[w]);
            }
        }
        self.gates_optimized += unused_gates;
        self.gates = without_unused_gates;
        // The indices of the output gates might have become invalid due to shifting the gates
        // around, so we need to shift the output indices as well:
        output_gates
            .into_iter()
            .map(|w| {
                if w > shift {
                    w - unused_before_gate[w - shift]
                } else {
                    w
                }
            })
            .collect()
    }

    pub fn build(mut self, output_gates: Vec<GateIndex>) -> Circuit {
        let output_gates = self.remove_unused_gates(output_gates);

        if PRINT_OPTIMIZATION_RATIO && self.gates_optimized > 0 {
            let optimized = self.gates_optimized * 100 / (self.gates.len() + self.gates_optimized);
            println!("Optimizations removed {optimized}% of all generated gates");
        }

        // All of the following shifts are necessary to translate between the intermediate circuit
        // representation (where indices 0 and 1 always refer to constant false and true values) and
        // the final representation (where there are no constant values and the constants have to be
        // 'built' by XOR'ing two identical input wire + using NOT):
        let input_shift = self.shift - 2;
        let shift_gate_index_if_necessary = |i: GateIndex| {
            if i <= 1 {
                i + input_shift
            } else if i < input_shift + 2 {
                i - 2
            } else {
                i
            }
        };
        let shift_gate_if_necessary = |gate: BuilderGate| match gate {
            BuilderGate::Xor(x, y) => {
                if x == 1 {
                    let y = shift_gate_index_if_necessary(y);
                    Gate::Not(y)
                } else if y == 1 {
                    let x = shift_gate_index_if_necessary(x);
                    Gate::Not(x)
                } else {
                    let x = shift_gate_index_if_necessary(x);
                    let y = shift_gate_index_if_necessary(y);
                    Gate::Xor(x, y)
                }
            }
            BuilderGate::And(x, y) => {
                let x = shift_gate_index_if_necessary(x);
                let y = shift_gate_index_if_necessary(y);
                Gate::And(x, y)
            }
        };
        let mut gates: Vec<Gate> = self
            .gates
            .into_iter()
            .map(shift_gate_if_necessary)
            .collect();
        gates.insert(0, Gate::Xor(0, 0)); // constant false
        gates.insert(1, Gate::Not(input_shift)); // constant true

        let mut panic_and_output =
            Vec::with_capacity(PANIC_RESULT_SIZE_IN_BITS + output_gates.len());
        let shift_indexes_if_necessary = |mut indexes: [usize; USIZE_BITS]| -> [usize; USIZE_BITS] {
            for wire in indexes.iter_mut() {
                *wire = shift_gate_index_if_necessary(*wire);
            }
            indexes
        };
        panic_and_output.push(shift_gate_index_if_necessary(
            self.panic_gates.result.has_panicked,
        ));
        panic_and_output.extend(shift_indexes_if_necessary(
            self.panic_gates.result.panic_type,
        ));
        panic_and_output.extend(shift_indexes_if_necessary(
            self.panic_gates.result.start_line,
        ));
        panic_and_output.extend(shift_indexes_if_necessary(
            self.panic_gates.result.start_column,
        ));
        panic_and_output.extend(shift_indexes_if_necessary(self.panic_gates.result.end_line));
        panic_and_output.extend(shift_indexes_if_necessary(
            self.panic_gates.result.end_column,
        ));

        panic_and_output.extend(output_gates.into_iter().map(shift_gate_index_if_necessary));

        Circuit {
            input_gates: self.input_gates,
            gates,
            output_gates: panic_and_output,
        }
    }

    pub fn push_panic_if(&mut self, cond: GateIndex, reason: PanicReason, meta: MetaInfo) {
        if let Some(existing_panic) = self.panic_gates.cache.get(&cond) {
            self.panic_gates.result = existing_panic.clone();
            return;
        }
        let already_panicked = self.panic_gates.result.has_panicked;
        self.panic_gates.result.has_panicked =
            self.push_or(self.panic_gates.result.has_panicked, cond);
        let current = PanicResult {
            has_panicked: 1,
            panic_type: reason.as_bits(),
            start_line: unsigned_as_usize_bits(meta.start.0 as u64),
            start_column: unsigned_as_usize_bits(meta.start.1 as u64),
            end_line: unsigned_as_usize_bits(meta.end.0 as u64),
            end_column: unsigned_as_usize_bits(meta.end.1 as u64),
        };
        for i in 0..self.panic_gates.result.start_line.len() {
            self.panic_gates.result.start_line[i] = self.push_mux(
                already_panicked,
                self.panic_gates.result.start_line[i],
                current.start_line[i],
            );
            self.panic_gates.result.start_column[i] = self.push_mux(
                already_panicked,
                self.panic_gates.result.start_column[i],
                current.start_column[i],
            );
            self.panic_gates.result.end_line[i] = self.push_mux(
                already_panicked,
                self.panic_gates.result.end_line[i],
                current.end_line[i],
            );
            self.panic_gates.result.end_column[i] = self.push_mux(
                already_panicked,
                self.panic_gates.result.end_column[i],
                current.end_column[i],
            );
        }
        for i in 0..current.panic_type.len() {
            self.panic_gates.result.panic_type[i] = self.push_mux(
                already_panicked,
                self.panic_gates.result.panic_type[i],
                current.panic_type[i],
            );
        }
        self.panic_gates
            .cache
            .insert(cond, self.panic_gates.result.clone());
    }

    pub fn peek_panic(&self) -> &CachedPanicResult {
        &self.panic_gates
    }

    pub fn replace_panic_with(&mut self, p: CachedPanicResult) -> CachedPanicResult {
        std::mem::replace(&mut self.panic_gates, p)
    }

    pub fn mux_panic(
        &mut self,
        condition: GateIndex,
        CachedPanicResult {
            result: t,
            cache: cache_t,
        }: &CachedPanicResult,
        CachedPanicResult {
            result: f,
            cache: cache_f,
        }: &CachedPanicResult,
    ) -> CachedPanicResult {
        let result = self.mux_uncached_panic(condition, t, f);
        let mut cache = HashMap::new();
        for k in cache_t.keys().chain(cache_f.keys()) {
            match (cache_t.get(k), cache_f.get(k)) {
                (None, None) => {}
                (None, Some(result)) | (Some(result), None) => {
                    cache.insert(*k, result.clone());
                }
                (Some(t), Some(f)) => {
                    cache.insert(*k, self.mux_uncached_panic(condition, t, f));
                }
            }
        }
        CachedPanicResult { result, cache }
    }

    fn mux_uncached_panic(
        &mut self,
        condition: GateIndex,
        t: &PanicResult,
        f: &PanicResult,
    ) -> PanicResult {
        let mut result = PanicResult::ok();
        result.has_panicked = self.push_mux(condition, t.has_panicked, f.has_panicked);
        for (i, (&if_true, &if_false)) in t.panic_type.iter().zip(f.panic_type.iter()).enumerate() {
            result.panic_type[i] = self.push_mux(condition, if_true, if_false);
        }
        for (i, (&if_true, &if_false)) in t.start_line.iter().zip(f.start_line.iter()).enumerate() {
            result.start_line[i] = self.push_mux(condition, if_true, if_false);
        }
        for (i, (&if_true, &if_false)) in
            t.start_column.iter().zip(f.start_column.iter()).enumerate()
        {
            result.start_column[i] = self.push_mux(condition, if_true, if_false);
        }
        for (i, (&if_true, &if_false)) in t.end_line.iter().zip(f.end_line.iter()).enumerate() {
            result.end_line[i] = self.push_mux(condition, if_true, if_false);
        }
        for (i, (&if_true, &if_false)) in t.end_column.iter().zip(f.end_column.iter()).enumerate() {
            result.end_column[i] = self.push_mux(condition, if_true, if_false);
        }
        result
    }

    pub fn mux_envs(
        &mut self,
        condition: usize,
        a: Env<Vec<GateIndex>>,
        b: Env<Vec<GateIndex>>,
    ) -> Env<Vec<GateIndex>> {
        if a.0.len() != b.0.len() {
            panic!("Cannot mux environments with different scopes: {a:?} vs. {b:?}");
        }
        let mut muxed = Env(vec![]);
        for (a, b) in a.0.iter().zip(b.0.iter()) {
            muxed.push();
            if a.len() != a.len() || !a.keys().all(|k| b.contains_key(k)) {
                panic!("Scopes have different bindings: {a:?} vs {b:?}");
            }
            for (identifier, binding_a) in a {
                let binding_b = b.get(identifier).unwrap();
                if binding_a.len() != binding_b.len() {
                    panic!("Bindings of variable '{identifier}' have different lengths: {binding_a:?} vs {binding_b:?}");
                }
                let mut binding = vec![0; binding_a.len()];
                for (i, (&if_true, &if_false)) in binding_a.iter().zip(binding_b.iter()).enumerate()
                {
                    binding[i] = self.push_mux(condition, if_true, if_false);
                }
                muxed.let_in_current_scope(identifier.clone(), binding);
            }
        }
        muxed
    }

    // - Constant evaluation (e.g. x ^ 0 == x; x ^ x == 0)
    // - Sub-expression sharing (wires are re-used if a gate with the same type and inputs exists)
    fn optimize_xor(&self, x: GateIndex, y: GateIndex) -> Option<GateIndex> {
        if x == 0 {
            return Some(y);
        } else if y == 0 {
            return Some(x);
        } else if x == y {
            return Some(0);
        } else if let Some(&x_negated) = self.negated.get(&x) {
            if x_negated == y {
                return Some(1);
            } else if y == 1 {
                return Some(x_negated);
            }
        } else if let Some(&y_negated) = self.negated.get(&y) {
            if y_negated == x {
                return Some(1);
            } else if x == 1 {
                return Some(y_negated);
            }
        }
        // Sub-expression sharing:
        if let Some(&wire) = self.get_cached(&BuilderGate::Xor(x, y)) {
            return Some(wire);
        }
        None
    }

    pub fn push_xor(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        if let Some(optimized) = self.optimize_xor(x, y) {
            self.gates_optimized += 1;
            optimized
        } else {
            if x >= self.shift && y >= self.shift {
                let gate_x = self.gates[x - self.shift];
                let gate_y = self.gates[y - self.shift];
                if let (BuilderGate::Xor(x1, x2), BuilderGate::Xor(y1, y2)) = (gate_x, gate_y) {
                    if x1 == y1 {
                        return self.push_xor(x2, y2);
                    } else if x1 == y2 {
                        return self.push_xor(x2, y1);
                    } else if x2 == y1 {
                        return self.push_xor(x1, y2);
                    } else if x2 == y2 {
                        return self.push_xor(x1, y1);
                    }
                } else if let (BuilderGate::And(x1, x2), BuilderGate::And(y1, y2)) =
                    (gate_x, gate_y)
                {
                    for (a1, a2, b1, b2) in [
                        (x1, x2, y1, y2),
                        (x1, x2, y2, y1),
                        (x2, x1, y1, y2),
                        (x2, x1, y2, y1),
                    ] {
                        if a1 == b1 {
                            if let Some(&a2_xor_b2) = self.get_cached(&BuilderGate::Xor(a2, b2)) {
                                if let Some(&wire) =
                                    self.get_cached(&BuilderGate::And(a1, a2_xor_b2))
                                {
                                    self.gates_optimized += 1;
                                    return wire;
                                }
                            }
                        }
                    }
                    for (a1, a2, b1, b2) in [
                        (x1, x2, y1, y2),
                        (x1, x2, y2, y1),
                        (x2, x1, y1, y2),
                        (x2, x1, y2, y1),
                    ] {
                        if a1 == b1 && !self.used.contains(&x) && !self.used.contains(&y) {
                            let a2_xor_b2_gate = BuilderGate::Xor(a2, b2);
                            self.gate_counter += 1;
                            self.gates.push(a2_xor_b2_gate);
                            let a2_xor_b2 = self.gate_counter - 1;
                            self.cache.insert(a2_xor_b2_gate, a2_xor_b2);

                            let gate = BuilderGate::And(a1, a2_xor_b2);
                            self.gate_counter += 1;
                            self.gates.push(gate);
                            self.cache.insert(gate, self.gate_counter - 1);
                            self.used.insert(a2_xor_b2);
                            return self.gate_counter - 1;
                        }
                    }
                }
            }
            if x >= self.shift {
                let gate_x = self.gates[x - self.shift];
                if let BuilderGate::Xor(x1, x2) = gate_x {
                    if x1 == y {
                        self.gates_optimized += 1;
                        return x2;
                    } else if x2 == y {
                        self.gates_optimized += 1;
                        return x1;
                    } else if let Some(&y_negated) = self.negated.get(&y) {
                        if x1 == y_negated {
                            return self.push_xor(x2, 1);
                        } else if x2 == y_negated {
                            return self.push_xor(x1, 1);
                        }
                    }
                }
            }
            if y >= self.shift {
                let gate_y = self.gates[y - self.shift];
                if let BuilderGate::Xor(y1, y2) = gate_y {
                    if x == y1 {
                        self.gates_optimized += 1;
                        return y2;
                    } else if x == y2 {
                        self.gates_optimized += 1;
                        return y1;
                    } else if let Some(&x_negated) = self.negated.get(&x) {
                        if x_negated == y1 {
                            return self.push_xor(1, y2);
                        } else if x_negated == y2 {
                            return self.push_xor(1, y1);
                        }
                    }
                }
            }
            let gate = BuilderGate::Xor(x, y);
            self.gate_counter += 1;
            self.gates.push(gate);
            let gate_index = self.gate_counter - 1;
            self.cache.insert(gate, gate_index);
            self.used.insert(x);
            self.used.insert(y);
            if x == 1 {
                self.negated.insert(y, gate_index);
                self.negated.insert(gate_index, y);
            }
            if y == 1 {
                self.negated.insert(x, gate_index);
                self.negated.insert(gate_index, x);
            }
            gate_index
        }
    }

    // - Constant evaluation (e.g. x & x == x; x & 1 == x; x & 0 == 0)
    // - Sub-expression sharing (wires are re-used if a gate with the same type and inputs exists)
    fn optimize_and(&self, x: GateIndex, y: GateIndex) -> Option<GateIndex> {
        if x == 0 || y == 0 {
            return Some(0);
        } else if x == 1 {
            return Some(y);
        } else if y == 1 || x == y {
            return Some(x);
        } else if let Some(&x_negated) = self.negated.get(&x) {
            if x_negated == y {
                return Some(0);
            }
        } else if let Some(&y_negated) = self.negated.get(&y) {
            if y_negated == x {
                return Some(0);
            }
        }
        // Sub-expression sharing:
        if let Some(&wire) = self.get_cached(&BuilderGate::And(x, y)) {
            return Some(wire);
        }
        None
    }

    pub fn push_and(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        if let Some(optimized) = self.optimize_and(x, y) {
            self.gates_optimized += 1;
            optimized
        } else {
            if x >= self.shift && y >= self.shift {
                let gate_x = self.gates[x - self.shift];
                let gate_y = self.gates[y - self.shift];
                if let (BuilderGate::And(x1, x2), BuilderGate::And(y1, y2)) = (gate_x, gate_y) {
                    if x1 == y1 || x2 == y1 {
                        return self.push_and(x, y2);
                    } else if x1 == y2 || x2 == y2 {
                        return self.push_and(x, y1);
                    }
                }
            }
            if x >= self.shift {
                let gate_x = self.gates[x - self.shift];
                if let BuilderGate::And(x1, x2) = gate_x {
                    if x1 == y || x2 == y {
                        self.gates_optimized += 1;
                        return x;
                    }
                    if let Some(&y_negated) = self.negated.get(&y) {
                        if x1 == y_negated || x2 == y_negated {
                            return 0;
                        }
                    }
                } else if let BuilderGate::Xor(x1, x2) = gate_x {
                    if let (Some(&x1_and_y), Some(&x2_and_y)) = (
                        self.get_cached(&BuilderGate::And(x1, y)),
                        self.get_cached(&BuilderGate::And(x2, y)),
                    ) {
                        return self.push_xor(x1_and_y, x2_and_y);
                    }
                }
            }
            if y >= self.shift {
                let gate_y = self.gates[y - self.shift];
                if let BuilderGate::And(y1, y2) = gate_y {
                    if x == y1 || x == y2 {
                        self.gates_optimized += 1;
                        return y;
                    }
                    if let Some(&x_negated) = self.negated.get(&x) {
                        if x_negated == y1 || x_negated == y2 {
                            return 0;
                        }
                    }
                } else if let BuilderGate::Xor(y1, y2) = gate_y {
                    if let (Some(&x_and_y1), Some(&x_and_y2)) = (
                        self.get_cached(&BuilderGate::And(x, y1)),
                        self.get_cached(&BuilderGate::And(x, y2)),
                    ) {
                        return self.push_xor(x_and_y1, x_and_y2);
                    }
                }
            }
            let gate = BuilderGate::And(x, y);
            self.gate_counter += 1;
            self.gates.push(gate);
            self.cache.insert(gate, self.gate_counter - 1);
            self.used.insert(x);
            self.used.insert(y);
            self.gate_counter - 1
        }
    }

    pub fn push_not(&mut self, x: GateIndex) -> GateIndex {
        self.push_xor(x, 1)
    }

    pub fn push_or(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        let xor = self.push_xor(x, y);
        let and = self.push_and(x, y);
        self.push_xor(xor, and)
    }

    pub fn push_eq(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        let xor = self.push_xor(x, y);
        self.push_xor(xor, 1)
    }

    pub fn push_eq_circuit(&mut self, x: &[GateIndex], y: &[GateIndex]) -> GateIndex {
        if x.len() != y.len() {
            // always false
            return 0;
        }
        let mut is_eq = 1;
        for (&x, &y) in x.iter().zip(y) {
            let bits_eq = self.push_eq(x, y);
            is_eq = self.push_and(is_eq, bits_eq)
        }
        is_eq
    }

    pub fn push_mux(&mut self, s: GateIndex, x0: GateIndex, x1: GateIndex) -> GateIndex {
        if x0 == x1 {
            return x0;
        }
        let x0_xor_x1 = self.push_xor(x0, x1);
        let nots = self.push_not(s);
        let swap = self.push_and(x0_xor_x1, nots);
        self.push_xor(x0, swap)
    }

    pub fn push_adder(
        &mut self,
        x: GateIndex,
        y: GateIndex,
        carry: GateIndex,
    ) -> (GateIndex, GateIndex) {
        // first half-adder:
        let wire_u = self.push_xor(x, y);
        let wire_v = self.push_and(x, y);
        // second half-adder:
        let wire_s = self.push_xor(wire_u, carry);
        let wire_w = self.push_and(wire_u, carry);

        let carry = self.push_or(wire_v, wire_w);
        (wire_s, carry)
    }

    pub fn push_multiplier(
        &mut self,
        x: GateIndex,
        y: GateIndex,
        z: GateIndex,
        carry: GateIndex,
    ) -> (GateIndex, GateIndex) {
        let x_and_y = self.push_and(x, y);
        self.push_adder(x_and_y, z, carry)
    }

    pub fn push_addition_circuit(
        &mut self,
        x: &[GateIndex],
        y: &[GateIndex],
    ) -> (Vec<GateIndex>, GateIndex, GateIndex) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let mut carry_prev = 0;
        let mut carry = 0;
        let mut sum = vec![0; bits];
        // sequence of full adders:
        for i in (0..bits).rev() {
            let (s, c) = self.push_adder(x[i], y[i], carry);
            sum[i] = s;
            carry_prev = carry;
            carry = c;
        }
        (sum, carry, carry_prev)
    }

    pub fn push_negation_circuit(&mut self, x: &[GateIndex]) -> Vec<GateIndex> {
        // flip bits and increment to get negate:
        let mut carry = 1;
        let mut neg = vec![0; x.len()];
        for i in (0..x.len()).rev() {
            let x = self.push_not(x[i]);
            // half-adder:
            neg[i] = self.push_xor(carry, x);
            carry = self.push_and(carry, x);
        }
        neg
    }

    pub fn push_subtraction_circuit(
        &mut self,
        x: &[GateIndex],
        y: &[GateIndex],
        is_signed: bool,
    ) -> (Vec<GateIndex>, GateIndex) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let mut x_extended = vec![0; bits + 1];
        x_extended[1..].copy_from_slice(x);
        if is_signed {
            x_extended[0] = x_extended[1];
        }
        let mut y_extended = vec![0; bits + 1];
        y_extended[1..].copy_from_slice(y);
        if is_signed {
            y_extended[0] = y_extended[1];
        }
        let y_negated = self.push_negation_circuit(&y_extended);

        let (mut sum_extended, _, _) = self.push_addition_circuit(&x_extended, &y_negated);
        let sign = sum_extended[0];
        let sum = sum_extended.split_off(1);
        let overflow = if is_signed {
            self.push_xor(sign, sum[0])
        } else {
            sign
        };
        (sum, overflow)
    }

    pub fn push_unsigned_division_circuit(
        &mut self,
        x: &[GateIndex],
        y: &[GateIndex],
    ) -> (Vec<GateIndex>, Vec<GateIndex>) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let mut quotient = vec![0; bits];
        let mut remainder = x.to_vec();
        for shift_amount in (0..bits).rev() {
            let mut overflow = 0;
            let mut y_shifted = vec![0; bits];
            for y in y.iter().copied().take(shift_amount) {
                overflow = self.push_or(overflow, y);
            }
            y_shifted[..(bits - shift_amount)]
                .clone_from_slice(&y[shift_amount..((bits - shift_amount) + shift_amount)]);

            let (x_sub, carry) = self.push_subtraction_circuit(&remainder, &y_shifted, false);
            let carry_or_overflow = self.push_or(carry, overflow);
            for i in 0..bits {
                remainder[i] = self.push_mux(carry_or_overflow, remainder[i], x_sub[i]);
            }
            let quotient_bit = self.push_not(carry);
            quotient[bits - shift_amount - 1] = self.push_mux(overflow, 0, quotient_bit);
        }
        (quotient, remainder)
    }

    pub fn push_signed_division_circuit(
        &mut self,
        x: &mut [GateIndex],
        y: &mut [GateIndex],
    ) -> (Vec<GateIndex>, Vec<GateIndex>) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let is_result_neg = self.push_xor(x[0], y[0]);
        let x_negated = self.push_negation_circuit(x);
        let x_sign_bit = x[0];
        for i in 0..bits {
            x[i] = self.push_mux(x_sign_bit, x_negated[i], x[i]);
        }
        let y_negated = self.push_negation_circuit(y);
        let y_sign_bit = y[0];
        for i in 0..bits {
            y[i] = self.push_mux(y_sign_bit, y_negated[i], y[i]);
        }
        let (mut quotient, mut remainder) = self.push_unsigned_division_circuit(x, y);
        let quot_neg = self.push_negation_circuit(&quotient);
        for i in 0..bits {
            quotient[i] = self.push_mux(is_result_neg, quot_neg[i], quotient[i]);
        }
        let rem_neg = self.push_negation_circuit(&remainder);
        for i in 0..bits {
            remainder[i] = self.push_mux(x_sign_bit, rem_neg[i], remainder[i]);
        }
        (quotient, remainder)
    }

    pub fn push_gt_circuit(&mut self, bits: usize, x: &[GateIndex], y: &[GateIndex]) -> GateIndex {
        // Sec. 3.2 in https://eprint.iacr.org/2009/411.pdf
        let mut carry = 0;
        for i in (0..bits).rev() {
            let x_xor_c = self.push_xor(x[i], carry);
            let y_xor_c = self.push_xor(y[i], carry);
            let not_y_xor_c = self.push_not(y_xor_c);
            let and = self.push_and(x_xor_c, not_y_xor_c);
            carry = self.push_xor(and, carry);
        }
        carry
    }

    // TODO use optimized gt (and lt) instead of this, also see issue
    // https://github.com/sine-fdn/garble-lang/issues/201 (robinhundt 31.07.25)
    pub fn push_comparator_circuit(
        &mut self,
        bits: usize,
        x: &[GateIndex],
        is_x_signed: bool,
        y: &[GateIndex],
        is_y_signed: bool,
    ) -> (GateIndex, GateIndex) {
        let mut acc_gt = 0;
        let mut acc_lt = 0;
        for i in 0..bits {
            let xor = self.push_xor(x[i], y[i]);

            let xor_and_x = self.push_and(xor, x[i]);
            let xor_and_y = self.push_and(xor, y[i]);
            let (gt, lt) = if i == 0 && (is_x_signed || is_y_signed) {
                (xor_and_y, xor_and_x)
            } else {
                (xor_and_x, xor_and_y)
            };

            let gt = self.push_or(gt, acc_gt);
            let lt = self.push_or(lt, acc_lt);

            let not_acc_gt = self.push_not(acc_gt);
            let not_acc_lt = self.push_not(acc_lt);

            acc_gt = self.push_and(gt, not_acc_lt);
            acc_lt = self.push_and(lt, not_acc_gt)
        }
        (acc_lt, acc_gt)
    }

    pub fn push_condswap(
        &mut self,
        s: GateIndex,
        x: GateIndex,
        y: GateIndex,
    ) -> (GateIndex, GateIndex) {
        if x == y {
            return (x, y);
        }
        let x_xor_y = self.push_xor(x, y);
        let swap = self.push_and(x_xor_y, s);
        let x_swapped = self.push_xor(x, swap);
        let y_swapped = self.push_xor(y, swap);
        (x_swapped, y_swapped)
    }

    pub fn push_sorter(
        &mut self,
        bits: usize,
        x: &[GateIndex],
        y: &[GateIndex],
    ) -> (Vec<GateIndex>, Vec<GateIndex>) {
        let gt = self.push_gt_circuit(bits, x, y);
        let mut min = vec![];
        let mut max = vec![];
        for (x, y) in x.iter().zip(y.iter()) {
            let (a, b) = self.push_condswap(gt, *x, *y);
            min.push(a);
            max.push(b);
        }
        (min, max)
    }

    pub fn push_bitonic_merger(
        &mut self,
        bits: usize,
        // Whether the output will be sorted in ascending or descending order
        ascending: bool,
        bitonic: &mut [Vec<GateIndex>],
    ) {
        if bitonic.len() <= 1 {
            return;
        }
        let m = bitonic.len().next_power_of_two() / 2; // prev power of two
        for i in 0..bitonic.len() - m {
            let x = &bitonic[i];
            let y = &bitonic[i + m];
            let (mut min, mut max) = self.push_sorter(bits, x, y);
            if !ascending {
                mem::swap(&mut min, &mut max);
            }
            bitonic[i] = min;
            bitonic[i + m] = max;
        }
        let (lower, upper) = bitonic.split_at_mut(m);
        self.push_bitonic_merger(bits, ascending, lower);
        self.push_bitonic_merger(bits, ascending, upper);
    }

    pub fn push_bitonic_sorter(&mut self, bits: usize, input: &mut [Vec<GateIndex>]) {
        fn push_bitonic_sorter_inner(
            c: &mut CircuitBuilder,
            bits: usize,
            ascending: bool,
            input: &mut [Vec<GateIndex>],
        ) {
            let num_elements = input.len();
            if num_elements <= 1 {
                return;
            }
            // assert_eq!(0, num_elements % 2, "Length: {}", num_elements);
            let (lower, upper) = input.split_at_mut(input.len() / 2);
            push_bitonic_sorter_inner(c, bits, !ascending, lower);
            push_bitonic_sorter_inner(c, bits, ascending, upper);
            c.push_bitonic_merger(bits, ascending, input);
        }
        push_bitonic_sorter_inner(self, bits, true, input);
    }
}

fn unsigned_as_usize_bits(n: u64) -> [usize; USIZE_BITS] {
    let mut bits = [0; USIZE_BITS];
    for (i, bit) in bits.iter_mut().enumerate().take(USIZE_BITS) {
        *bit = ((n >> (USIZE_BITS - 1 - i)) & 1) as usize;
    }
    bits
}
