//! A converter to convert between the Garble Circuit and the Bristol fashion circuit format.
//! https://nigelsmart.github.io/MPC-Circuits/

use crate::circuit::{Circuit, Gate, PANIC_RESULT_SIZE_IN_BITS};
use std::{
    collections::HashSet,
    fs::File,
    io::{BufRead, BufReader, Write},
    num::ParseIntError,
    path::Path,
};

/// An error that occurred during compilation.
#[derive(Debug)]
pub enum ConverterError {
    /// Some input wires are also output wires.
    ToBristolError(ToBristolError),
    /// An error occurred while writing to the file.
    FromBristolError(FromBristolError),
}

/// An error that occurred during compilation.
#[derive(Debug)]
#[non_exhaustive]
pub enum ToBristolError {
    /// Some input wires are also output wires.
    OutputWireIsInput,
    /// An error occurred while writing to the file.
    IoError(std::io::Error),
}

/// An error that occurred during compilation.
#[derive(Debug)]
#[non_exhaustive]
pub enum FromBristolError {
    /// An error occurred while writing to the file.
    IoError(std::io::Error),
    /// An error occurred while parsing the number of inputs, input wires or output wires as integers.
    ParseIntError(ParseIntError),
    /// An unknown gate was encountered.
    UnknownGate(String),
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
    /// The output wire is not a valid wire in the circuit.
    InvalidWireIndex(usize),
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
        }
    }
}

impl std::fmt::Display for ToBristolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToBristolError::OutputWireIsInput => f.write_str(
                "Output wire is also an input wire, which is not allowed in Bristol fashion format",
            ),
            ToBristolError::IoError(e) => f.write_fmt(format_args!("IO error: {}", e)),
        }
    }
}

impl std::fmt::Display for FromBristolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FromBristolError::IoError(e) => f.write_fmt(format_args!("IO error: {}", e)),
            FromBristolError::ParseIntError(e) => {
                f.write_fmt(format_args!("Parse integer error while parsing number of inputs, input wires or output wires: {}", e))
            }
            FromBristolError::UnknownGate(gate) => {
                f.write_fmt(format_args!("Unknown gate: {}", gate))
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
            FromBristolError::InvalidWireIndex(wire) => f.write_fmt(format_args!(
                "Wire index larger than number of wires: {}",
                wire
            )),
        }
    }
}

impl std::error::Error for ConverterError {}

impl From<std::io::Error> for ToBristolError {
    fn from(e: std::io::Error) -> Self {
        ToBristolError::IoError(e)
    }
}

impl From<std::io::Error> for FromBristolError {
    fn from(e: std::io::Error) -> Self {
        FromBristolError::IoError(e)
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

impl From<ParseIntError> for FromBristolError {
    fn from(e: ParseIntError) -> Self {
        FromBristolError::ParseIntError(e)
    }
}

impl Circuit {
    /// Converts a Circuit into a [Bristol fashion circuit format](https://nigelsmart.github.io/MPC-Circuits/).
    /// We support the 'basic' bristol format (no MAND gates), and we only support the following gates: XOR, AND, INV.
    /// Gates EQ and EQW are not supported, though might occur in the circuit.
    ///
    /// The first line contains the number of gates, and then the number of wires in the circuit.
    /// The second line contains the number of input values, and the number of bits per input value.
    /// The third line contains the number of output values, and the number of bits per output value.
    /// The remaining lines contain the gates in the circuit, where each line contains the number of input
    /// wires, the number of output wires, then lists the input and output wires and the gate type (XOR, AND, INV).
    ///
    /// Garble circuits can contain panic gates, which are not supported in the Bristol format.
    /// Hence, the panic gates are removed from the circuit, and the output wires are adjusted accordingly.
    pub fn format_as_bristol(&self, path: &Path) -> Result<(), ToBristolError> {
        let mut circuit = self;
        let total_input_gates = circuit.input_gates.iter().sum::<usize>();
        let mut total_gates = circuit.gates.len();
        let mut total_wires = total_gates + total_input_gates;

        // Though Garble provides panic support, the bristol fashion format and other circuit
        // compilers do not, hence we remove the bits of the output that correspond to panic support,
        // assuming that we do the conversion to use the circuit in a different compiler.
        let mut output_gates = circuit.output_gates[PANIC_RESULT_SIZE_IN_BITS..].to_vec();

        // Theoretically, it could be possible that input wires are also output wires in Garble.
        // This, however, is strongly discouraged and not supported in Bristol fashion format since
        // it reveals information about the input.
        let input_wire_set: HashSet<_> = (0..total_input_gates).collect();
        if output_gates.iter().any(|w| input_wire_set.contains(w)) {
            return Err(ToBristolError::OutputWireIsInput);
        }

        // Deal with duplicate output wires that is possible in Garble by simulating "identity" gates using two Xor
        // gates, i.e., x XOR x XOR x = x, since the Bristol format requires every output bit to be a separate wire.
        let mut seen = HashSet::new();
        let mut mod_circuit = None;
        let mut wire_max = total_wires;

        for out in &mut output_gates {
            let inserted = seen.insert(*out);
            if !inserted {
                println!(
                    "Output wire {} is duplicated, simulating identity gate",
                    out
                );
                let circuit = mod_circuit.get_or_insert_with(|| circuit.clone());
                // This output wire (always false) with index wire_max will be used to simulate the identity gate.
                circuit.gates.push(Gate::Xor(*out, *out));
                // We XOR the result of wire_max (false) with the wire *out to simulate the identity gate.
                circuit.gates.push(Gate::Xor(*out, wire_max));
                *out = wire_max + 1;
                wire_max += 2;
                total_wires += 2;
                total_gates += 2;
            }
        }
        // if we modified the circuit, set the circuit reference to the modified one
        if let Some(c) = &mod_circuit {
            circuit = c;
        }

        // Create the file that will contain the circuit described in Bristol fashion.
        let mut file = File::create(path)?;
        // The first line contains the number of gates, and then the number of wires in the circuit.
        writeln!(file, "{} {}", total_gates, total_wires)?;
        // The second line contains the number of input values, and the number of bits per input value.
        // Note that inputs in the resulting bristol circuit correspond to the input of the computing parties in
        // ascending order.
        write!(file, "{} ", circuit.input_gates.len())?;
        for &input_len in &circuit.input_gates {
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
        for (i, gate) in circuit.gates.iter().enumerate() {
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

    /// Converts a Bristol fashion circuit format into a Garble Circuit.
    /// We support the 'basic' bristol format (no MAND gates), and we only support the following gates: XOR, AND, INV.
    /// Gates EQ and EQW are not supported, though might occur in the bristol circuit.
    pub fn bristol_to_garble(path: &Path) -> Result<Circuit, FromBristolError> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let lines_res: Result<Vec<String>, std::io::Error> = reader.lines().collect();
        let lines_str = lines_res?;
        let mut lines = lines_str.into_iter();

        // Parse wire and gate counts
        let (wires_num, _gates_num) = {
            let (parts, line_str) = parse_line(lines.next())?;
            if parts.len() != 2 {
                return Err(FromBristolError::MalformedLine(line_str));
            }
            (parts[1], parts[0])
        };

        // Parse input line
        // The conversion assumes that each party provides one of the inputs in ascending order of their party IDs.
        let (input_gates, input_wires_num) = {
            let (parts, line_str) = parse_line(lines.next())?;
            if parts.len() < 2 {
                return Err(FromBristolError::MalformedLine(line_str));
            }
            let input_gates = parts[1..].to_vec();
            let expected_parties = parts[0];
            if input_gates.len() != expected_parties {
                return Err(FromBristolError::InputPartiesMismatch(
                    input_gates.len(),
                    expected_parties,
                ));
            }
            let input_wires: usize = input_gates.iter().sum();
            (input_gates, input_wires)
        };

        // Parse output line
        let (mut output_gates, num_output_wires) = {
            let (parts, line_str) = parse_line(lines.next())?;
            if parts.len() < 2 {
                return Err(FromBristolError::MalformedLine(line_str));
            }
            let num_outputs = parts[0];
            let gates_per_output = parts[1..].to_vec();
            if gates_per_output.len() != num_outputs {
                return Err(FromBristolError::OutputCountMismatch(
                    gates_per_output.len(),
                    num_outputs,
                ));
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
                return Err(FromBristolError::MalformedLine(line_str));
            }
            let num_inputs: usize = parts[0].parse()?;
            let num_outputs: usize = parts[1].parse()?;
            if num_outputs != 1 || parts.len() != num_inputs + 4 {
                return Err(FromBristolError::MalformedLine(line_str));
            }
            let input_wires: Vec<usize> = parts[2..(2 + num_inputs)]
                .iter()
                .map(|s| s.parse::<usize>().map_err(Into::into))
                .collect::<Result<_, FromBristolError>>()?;
            let output_wire: usize = parts[2 + num_inputs].parse()?;
            // Validate input wires and output wire are within bounds
            if let Some(&ind) = input_wires.iter().find(|&&w| w >= wires_num) {
                return Err(FromBristolError::InvalidWireIndex(ind));
            }
            if output_wire >= wires_num {
                return Err(FromBristolError::InvalidWireIndex(output_wire));
            }

            let gate_type = parts.last().ok_or(FromBristolError::MissingGateType)?;

            // Check if the output wire is an output gate

            if output_wire >= wires_num - num_output_wires {
                output_gates[output_wire - (wires_num - num_output_wires)] = next_wire;
            }

            wires_map[output_wire] = next_wire;
            next_wire += 1;

            let gate = match *gate_type {
                "XOR" | "AND" => {
                    if input_wires.len() != 2 {
                        return Err(FromBristolError::MalformedLine(line_str));
                    }
                    if *gate_type == "XOR" {
                        Gate::Xor(wires_map[input_wires[0]], wires_map[input_wires[1]])
                    } else {
                        Gate::And(wires_map[input_wires[0]], wires_map[input_wires[1]])
                    }
                }
                "INV" => {
                    if input_wires.len() != 1 {
                        return Err(FromBristolError::MalformedLine(line_str));
                    }
                    Gate::Not(wires_map[input_wires[0]])
                }
                _ => {
                    return Err(FromBristolError::UnknownGate(gate_type.to_string()));
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
