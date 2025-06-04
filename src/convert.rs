//! A converter to convert between the Garble Circuit and the Bristol fashion circuit format.
//! https://nigelsmart.github.io/MPC-Circuits/

use crate::circuit::{Circuit, Gate, PANIC_RESULT_SIZE_IN_BITS};
use std::{
    collections::HashSet,
    fs::File,
    io::{BufRead, BufReader, Write},
};

/// An error that occurred during compilation.
#[derive(Debug)]
pub enum ConverterError {
    /// Some input wires are also output wires.
    ToBristolError(ToBristolError),
    /// An error occurred while writing to the file.
    FromBristolError(FromBristolError),
    /// An error occurred while writing to the file.
    IoError(std::io::Error),
}

/// An error that occurred during compilation.
#[derive(Debug)]
pub enum ToBristolError {
    /// Some input wires are also output wires.
    OutputWireIsInput,
}

/// An error that occurred during compilation.
#[derive(Debug)]
pub enum FromBristolError {
    /// An unknown gate was encountered.
    UnknownGate(String),
    /// Missing number of inputs in the gate definition.
    MissingNumberOfInputs,
    /// Missing input wires in the gate definition.
    MissingInputWires,
    /// Missing output wires in the gate definition.
    MissingOutputWires,
    /// Missing gate type in the gate definition.
    MissingGateType,
    /// An error occurred while parsing the file.
    OtherParseError(String),
    /// The number of input wires does not match the number of parties.
    InputPartiesMismatch(usize, usize),
    /// The number of output wires does not match the number of output gates.
    OutputCountMismatch(usize, usize),
    /// Missing line in the Bristol fashion circuit file.
    MissingLine,
    /// Malformed Bristol fashion circuit file.
    MalformedLine(String),
}

impl std::fmt::Display for ConverterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConverterError::ToBristolError(e) => {
                f.write_fmt(format_args!("Garble to Bristol error: {}", e))
            }
            ConverterError::FromBristolError(e) => {
                f.write_fmt(format_args!("Bristol to Garble error: {}", e))
            }
            ConverterError::IoError(e) => f.write_fmt(format_args!("IO error: {}", e)),
        }
    }
}

impl std::fmt::Display for ToBristolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToBristolError::OutputWireIsInput => f.write_str(
                "Output wire is also an input wire, which is not allowed in Bristol fashion format",
            ),
        }
    }
}

impl std::fmt::Display for FromBristolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FromBristolError::UnknownGate(gate) => {
                f.write_fmt(format_args!("Unknown gate: {}", gate))
            }
            FromBristolError::MissingNumberOfInputs => {
                f.write_str("Missing number of inputs in gate definition")
            }
            FromBristolError::MissingInputWires => {
                f.write_str("Missing input wires in gate definition")
            }
            FromBristolError::MissingOutputWires => {
                f.write_str("Missing output wires in gate definition")
            }
            FromBristolError::MissingGateType => {
                f.write_str("Missing gate type in gate definition")
            }
            FromBristolError::OtherParseError(e) => f.write_fmt(format_args!("Parse error: {}", e)),
            FromBristolError::InputPartiesMismatch(actual, expected) => f.write_fmt(format_args!(
                "Input parties mismatch: actual {}, expected {}",
                actual, expected
            )),
            FromBristolError::OutputCountMismatch(actual, expected) => f.write_fmt(format_args!(
                "Output count mismatch: actual {}, expected {}",
                actual, expected
            )),
            FromBristolError::MissingLine => f.write_str("Missing line in the file"),
            FromBristolError::MalformedLine(line) => {
                f.write_fmt(format_args!("Malformed line: {}", line))
            }
        }
    }
}

impl std::error::Error for ConverterError {}

impl From<std::io::Error> for ConverterError {
    fn from(e: std::io::Error) -> Self {
        ConverterError::IoError(e)
    }
}

impl From<FromBristolError> for ConverterError {
    fn from(e: FromBristolError) -> Self {
        ConverterError::FromBristolError(e)
    }
}

impl From<ToBristolError> for ConverterError {
    fn from(e: ToBristolError) -> Self {
        ConverterError::ToBristolError(e)
    }
}

/// Converts a Circuit into a [Bristol fashion circuit format](https://nigelsmart.github.io/MPC-Circuits/).
///
/// The 'basic' bristol format is a simple text format that describes a circuit in terms of its gates.
///
/// The first line contains the number of gates, and then the number of wires in the circuit.
/// The second line contains the number of input values, and the number of bits per input value.
/// The third line contains the number of output values, and the number of bits per output value.
/// The remaining lines contain the gates in the circuit, where each line contains the number of input
/// wires, the number of output wires, then lists the input and output wires and the gate type (XOR, AND, INV).
///
/// Garble circuits can contain panic gates, which are not supported in the Bristol format.
/// Hence, the panic gates are removed from the circuit, and the output wires are adjusted accordingly.
pub(crate) fn garble_to_bristol(circuit: Circuit, path: &str) -> Result<(), ConverterError> {
    let mut mod_circuit = circuit.clone();
    let total_input_gates = mod_circuit.input_gates.iter().sum::<usize>();
    let mut total_gates = mod_circuit.gates.len();
    let mut total_wires = total_gates + total_input_gates;

    // Though Garble provides panic support, the bristol fashion format and other circuit
    // compilers do not, hence we remove the bits of the output that correspond to panic support,
    // assuming that we do the conversion to use the circuit in a different compiler.
    let mut output_gates = mod_circuit.output_gates[PANIC_RESULT_SIZE_IN_BITS..].to_vec();

    // Theoretically, it could be possible that input wires are also output wires in Garble.
    // This, however, is strongly discouraged and not supported in Bristol fashion format since
    // it reveals information about the input.
    let input_wire_set: HashSet<_> = (0..total_input_gates).collect();
    if output_gates.iter().any(|w| input_wire_set.contains(w)) {
        return Err(ToBristolError::OutputWireIsInput.into());
    }

    // Deal with duplicate output wires that is possible in Garble by simulating "identity" gates using two Xor
    // gates, i.e., x XOR x XOR x = x, since the Bristol format requires every output bit to be a separate wire.
    let mut seen = HashSet::new();
    let mut wire_max = total_wires;
    for out in &mut output_gates {
        if !seen.insert(*out) {
            mod_circuit.gates.push(Gate::Xor(*out, *out));
            mod_circuit.gates.push(Gate::Xor(*out, wire_max));
            *out = wire_max + 1;
            wire_max += 2;
            total_wires += 2;
            total_gates += 2;
        }
    }

    // Create the file that will contain the circuit described in Bristol fashion.
    let mut file = File::create(path)?;
    // The first line contains the number of gates, and then the number of wires in the circuit.
    writeln!(file, "{} {}", total_gates, total_wires)?;
    // The second line contains the number of input values, and the number of bits per input value.
    write!(file, "{} ", mod_circuit.input_gates.len())?;
    for &input_len in &mod_circuit.input_gates {
        write!(file, "{} ", input_len)?;
    }
    writeln!(file)?;
    // The third line contains the number of output values, and the number of bits per output value.
    writeln!(file, "1 {}", output_gates.len())?;
    writeln!(file)?;

    // In order to convert the circuit to the Bristol format, we need to create a mapping
    // from the wires in the circuit to the wires in the Bristol format, where we need to make
    // sure that the last wires contain the output in the right order.
    let mut wires_map = vec![0; total_wires];
    for (i, wire) in wires_map.iter_mut().take(total_input_gates).enumerate() {
        *wire = i;
    }

    let mut out_idx = 0;
    for (i, wire) in wires_map.iter_mut().enumerate().skip(total_input_gates) {
        if let Some(idx) = output_gates.iter().position(|&x| x == i) {
            *wire = total_wires - output_gates.len() + idx;
            out_idx += 1;
        } else {
            *wire = i - out_idx;
        }
    }

    // Write the gates to the file in the Bristol format.
    for (i, gate) in mod_circuit.gates.iter().enumerate() {
        let (gate_type, inputs): (&str, Vec<usize>) = match gate {
            Gate::Xor(x, y) => ("XOR", vec![wires_map[*x], wires_map[*y]]),
            Gate::And(x, y) => ("AND", vec![wires_map[*x], wires_map[*y]]),
            Gate::Not(x) => ("INV", vec![wires_map[*x]]),
        };

        let input_str = inputs
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" ");
        let output_idx = wires_map[i + total_input_gates];

        writeln!(
            file,
            "{} 1 {} {} {}",
            inputs.len(),
            input_str,
            output_idx,
            gate_type
        )?;
    }

    Ok(())
}

/// Converts a Bristol fashion circuit format into a Garble Circuit. Important to note that
/// the Bristol format does not support panic gates, hence the panic gates are removed from the
/// circuit.
pub(crate) fn bristol_to_garble(path: &str) -> Result<Circuit, ConverterError> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut lines = reader.lines().map_while(Result::ok);

    // Parse wire and gate counts
    let (wires_num, _gates_num) = {
        let (parts, line_str) = parse_line(lines.next())?;
        if parts.len() != 2 {
            return Err(FromBristolError::MalformedLine(line_str).into());
        }
        (parts[1], parts[0])
    };

    // Parse input line
    let (input_gates, input_wires_num) = {
        let (parts, line_str) = parse_line(lines.next())?;
        if parts.len() < 2 {
            return Err(FromBristolError::MalformedLine(line_str).into());
        }
        let input_gates = parts[1..].to_vec();
        let expected_parties = parts[0];
        if input_gates.len() != expected_parties {
            return Err(FromBristolError::InputPartiesMismatch(
                input_gates.len(),
                expected_parties,
            )
            .into());
        }
        let input_wires: usize = input_gates.iter().sum();
        (input_gates, input_wires)
    };

    // Parse output line
    let (mut output_gates, num_output_wires) = {
        let (parts, line_str) = parse_line(lines.next())?;
        if parts.len() < 2 {
            return Err(FromBristolError::MalformedLine(line_str).into());
        }
        let num_outputs = parts[0];
        let gates_per_output = parts[1..].to_vec();
        if gates_per_output.len() != num_outputs {
            return Err(
                FromBristolError::OutputCountMismatch(gates_per_output.len(), num_outputs).into(),
            );
        }
        let num_output_wires = gates_per_output.iter().sum::<usize>();
        (vec![0; num_output_wires], num_output_wires)
    };

    // Create the wires map to map the wires in the Bristol format to the wires in the Garble format.
    let mut wires_map = vec![0; wires_num];
    for (i, wire) in wires_map.iter_mut().take(input_wires_num).enumerate() {
        *wire = i;
    }
    let mut next_wire = input_wires_num;

    // Parse gates
    let mut gates = Vec::new();
    for line_str in lines {
        let parts: Vec<&str> = line_str.split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }
        if parts.len() < 5 {
            return Err(FromBristolError::MalformedLine(line_str).into());
        }
        let num_inputs: usize = parts[0]
            .parse()
            .map_err(|_| FromBristolError::MissingNumberOfInputs)?;
        if parts.len() != num_inputs + 4 {
            return Err(FromBristolError::MalformedLine(line_str).into());
        }
        let input_wires: Vec<usize> = parts[2..(2 + num_inputs)]
            .iter()
            .map(|s| {
                s.parse::<usize>()
                    .map_err(|_| FromBristolError::MissingInputWires)
            })
            .collect::<Result<_, _>>()?;
        let output_wire: usize = parts[2 + num_inputs]
            .parse()
            .map_err(|_| FromBristolError::MissingOutputWires)?;
        let gate_type = parts.last().ok_or(FromBristolError::MissingGateType)?;

        // Check if the output wire is an output gate
        if output_wire < wires_num && output_wire >= wires_num - num_output_wires {
            output_gates[output_wire - (wires_num - num_output_wires)] = next_wire;
        }

        wires_map[output_wire] = next_wire;
        next_wire += 1;

        let gate = match *gate_type {
            "XOR" | "AND" => {
                if input_wires.len() != 2 {
                    return Err(FromBristolError::MalformedLine(line_str).into());
                }
                if *gate_type == "XOR" {
                    Gate::Xor(wires_map[input_wires[0]], wires_map[input_wires[1]])
                } else {
                    Gate::And(wires_map[input_wires[0]], wires_map[input_wires[1]])
                }
            }
            "INV" => {
                if input_wires.len() != 1 {
                    return Err(FromBristolError::MalformedLine(line_str).into());
                }
                Gate::Not(wires_map[input_wires[0]])
            }
            _ => {
                return Err(FromBristolError::UnknownGate(gate_type.to_string()).into());
            }
        };
        gates.push(gate);
    }

    Ok(Circuit {
        input_gates,
        gates,
        output_gates,
    })
}

/// Parses a line from the Bristol format file and returns a vector of usize.
pub fn parse_line(line: Option<String>) -> Result<(Vec<usize>, String), FromBristolError> {
    let line_str = line.ok_or(FromBristolError::MissingLine)?;

    let parts: Vec<usize> = line_str
        .split_whitespace()
        .map(|s| {
            s.parse::<usize>()
                .map_err(|e| FromBristolError::OtherParseError(e.to_string()))
        })
        .collect::<Result<_, _>>()?;

    Ok((parts, line_str))
}
