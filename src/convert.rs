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
    OutputWireIsInput,
    /// An unknown gate was encountered.
    UnknownGate(String),
    /// An error occurred while writing to the file.
    FileWrite(std::io::Error),
    /// An error occurred while parsing the file.
    ParseError(String),
    /// The number of input wires does not match the number of parties.
    InputPartiesMismatch(usize, usize),
    /// The number of output wires does not match the number of output gates.
    OutputCountMismatch(usize, usize),
}

impl From<std::io::Error> for ConverterError {
    fn from(e: std::io::Error) -> Self {
        ConverterError::FileWrite(e)
    }
}

/// Converts a Circuit into a [Bristol fashion circuit format](https://nigelsmart.github.io/MPC-Circuits/).
///
/// The bristol format is a simple text format that describes a circuit in terms of its gates.
/// Each line of the file describes a gate, with the first line containing the number of parties,
/// the number of wires, and the number of gates.
pub(crate) fn garble_to_bristol(circuit: &mut Circuit, path: &str) -> Result<(), ConverterError> {
    let total_input_gates = circuit.input_gates.iter().sum::<usize>();
    let mut total_gates = circuit.gates.len();
    let mut total_wires = total_gates + total_input_gates;

    // Though Garble provides panic support, the bristol fashion format and other circuit
    // compilers do not, hence we remove the bits of the output that correcpond to panic support,
    // assuming that we do the conversion to use the circuit in a different compiler.
    let mut output_gates = circuit.output_gates[PANIC_RESULT_SIZE_IN_BITS..].to_vec();

    // Theoretically, it could be possible that input wires are also output wires in Garble.
    // This, however, is strongly discouraged and not supported in Bristol fashion format since
    // it reveals information about the input.
    let input_wire_set: HashSet<_> = (0..total_input_gates).collect();
    if output_gates.iter().any(|w| input_wire_set.contains(w)) {
        return Err(ConverterError::OutputWireIsInput);
    }

    // Deal with duplicate output wires that is possible in Garble by simulate "identity" gates using two Xor
    // gates, i.e., x XOR x XOR x = x, since the Bristol format requires every output bit to be a separate wire.
    let mut seen = HashSet::new();
    let mut wire_max = total_wires;
    for out in &mut output_gates {
        if !seen.insert(*out) {
            circuit.gates.push(Gate::Xor(*out, *out));
            circuit.gates.push(Gate::Xor(*out, wire_max));
            *out = wire_max + 1;
            wire_max += 2;
            total_wires += 2;
            total_gates += 2;
        }
    }

    // Create the file that will contain the circuit described in Bristol fashion.
    let mut file = File::create(path).map_err(ConverterError::FileWrite)?;
    // The first line contains the number of parties, the number of wires, and the number of gates.
    writeln!(file, "{} {}", total_gates, total_wires).map_err(ConverterError::FileWrite)?;
    // The second line contains the number of parties, and the number of input wires per party.
    write!(file, "{} ", circuit.input_gates.len()).map_err(ConverterError::FileWrite)?;
    for &input_len in &circuit.input_gates {
        write!(file, "{} ", input_len).map_err(ConverterError::FileWrite)?;
    }
    writeln!(file).map_err(ConverterError::FileWrite)?;
    // The third line contains the number of output wires.
    writeln!(file, "1 {}", output_gates.len()).map_err(ConverterError::FileWrite)?;
    writeln!(file).map_err(ConverterError::FileWrite)?;

    // In order to convert the circuit to the Bristol format, we need to create a mapping
    // from the wires in the circuit to the wires in the Bristol format, where we need to make
    // sure that the last wires contain the output in the right order.
    let mut wires_map = vec![0; total_wires];
    for (i, wire) in wires_map.iter_mut().take(total_input_gates).enumerate() {
        *wire = i;
    }

    let mut out_idx = 0;
    for (i, wire) in wires_map
        .iter_mut()
        .enumerate()
        .take(total_wires)
        .skip(total_input_gates)
    {
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
        )
        .map_err(ConverterError::FileWrite)?;
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
        let parts = parse_line(lines.next())?;
        (parts[1], parts[0])
    };

    // Parse input line
    let (input_gates, input_wires_num) = {
        let parts = parse_line(lines.next())?;
        let input_gates = parts[1..].to_vec();
        let expected_parties = parts[0];
        if input_gates.len() != expected_parties {
            return Err(ConverterError::InputPartiesMismatch(
                input_gates.len(),
                expected_parties,
            ));
        }
        let input_wires: usize = input_gates.iter().sum();
        (input_gates, input_wires)
    };

    // Parse output line
    let (mut output_gates, num_output_wires) = {
        let parts = parse_line(lines.next())?;
        let num_outputs = parts[0];
        let gates_per_output = parts[1..].to_vec();
        if gates_per_output.len() != num_outputs {
            return Err(ConverterError::OutputCountMismatch(
                gates_per_output.len(),
                num_outputs,
            ));
        }
        let total_outputs = gates_per_output.iter().sum();
        let num_output_wires = gates_per_output.iter().sum::<usize>();
        (vec![0; total_outputs], num_output_wires)
    };

    // Create the wires map to map the wires in the Bristol format to the wires in the Garble format.
    let mut wires_map = vec![0; wires_num];
    for (i, wire) in wires_map.iter_mut().take(input_wires_num).enumerate() {
        *wire = i;
    }
    let mut next_wire = input_wires_num;

    // Parse gates
    let mut gates = Vec::new();
    for line in lines {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 4 {
            continue;
        }

        let num_inputs: usize = parts[0]
            .parse()
            .map_err(|_| ConverterError::ParseError("Missing number of inputs".to_string()))?;
        let input_wires: Vec<usize> = parts[2..(2 + num_inputs)]
            .iter()
            .map(|s| {
                s.parse::<usize>()
                    .map_err(|_| ConverterError::ParseError("Missing input wires".to_string()))
            })
            .collect::<Result<_, _>>()?;
        let output_wire: usize = parts[2 + num_inputs]
            .parse()
            .map_err(|_| ConverterError::ParseError("Missing output wires".to_string()))?;
        let gate_type = parts
            .last()
            .ok_or_else(|| ConverterError::ParseError("Missing gate type".to_string()))?;

        // Check if the output wire is an output gate
        if output_wire < wires_num && output_wire >= wires_num - num_output_wires {
            output_gates[output_wire - (wires_num - num_output_wires)] = next_wire;
        }

        wires_map[output_wire] = next_wire;
        next_wire += 1;

        let gate = match *gate_type {
            "XOR" => Gate::Xor(wires_map[input_wires[0]], wires_map[input_wires[1]]),
            "AND" => Gate::And(wires_map[input_wires[0]], wires_map[input_wires[1]]),
            "INV" => Gate::Not(wires_map[input_wires[0]]),
            _ => {
                return Err(ConverterError::UnknownGate(format!(
                    "Invalid gate type: {}",
                    gate_type
                )));
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
pub fn parse_line(line: Option<String>) -> Result<Vec<usize>, ConverterError> {
    let line_str =
        line.ok_or_else(|| std::io::Error::new(std::io::ErrorKind::Other, "Missing line"))?;
    line_str
        .split_whitespace()
        .map(|s| {
            s.parse::<usize>()
                .map_err(|e| ConverterError::ParseError(e.to_string()))
        })
        .collect()
}
