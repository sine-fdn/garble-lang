use garble_lang::{
    circuit::{Circuit, PANIC_RESULT_SIZE_IN_BITS},
    compile,
    convert::{FromBristolError, ToBristolError, parse_line},
};

use std::{
    fs::File,
    io::{BufRead, BufReader, Write},
    path::Path,
};

use tempfile::NamedTempFile;

/// Evaluates a Bristol format circuit using the given inputs.
fn bristol_eval(path: &Path, inputs: &[Vec<bool>]) -> Result<Vec<bool>, FromBristolError> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut lines = reader.lines().map_while(Result::ok);

    // Parse wire and gate counts
    let (wires_num, _gates_num) = {
        let (parts, line_str) = parse_line(lines.next())?;
        if parts.len() != 2 {
            return Err(FromBristolError::MalformedLine(line_str));
        }
        (parts[1], parts[0])
    };

    // Skip the line with the input parts
    lines.next();

    // Parse output parts
    let (output_parts, line_str) = parse_line(lines.next())?;
    if output_parts.len() < 2 {
        return Err(FromBristolError::MalformedLine(line_str));
    }
    let num_output_wires: usize = output_parts[1..].iter().sum();

    // Bristol eval
    let mut wires = vec![false; wires_num];
    let mut idx = 0;
    // Fill the input wires
    for inp in inputs {
        for input in inp {
            wires[idx] = *input;
            idx += 1;
        }
    }

    // Parse gates
    for line in lines {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }
        if parts.len() < 4 {
            return Err(FromBristolError::MalformedLine(line_str));
        }
        let num_inputs: usize = parts[0].parse().map_err(|_| {
            FromBristolError::OtherParseError("Missing number of inputs".to_string())
        })?;
        if parts.len() != num_inputs + 4 {
            return Err(FromBristolError::MalformedLine(line_str));
        }
        let input_wires: Vec<usize> = parts[2..(2 + num_inputs)]
            .iter()
            .map(|s| {
                s.parse::<usize>().map_err(|_| {
                    FromBristolError::OtherParseError("Missing input wires".to_string())
                })
            })
            .collect::<Result<_, _>>()?;
        let output_wire: usize = parts[2 + num_inputs]
            .parse()
            .map_err(|_| FromBristolError::OtherParseError("Missing output wires".to_string()))?;
        let gate_type = parts
            .last()
            .ok_or_else(|| FromBristolError::OtherParseError("Missing gate type".to_string()))?;

        match *gate_type {
            "XOR" | "AND" => {
                if input_wires.len() != 2 {
                    return Err(FromBristolError::MalformedLine(line_str));
                }
                if *gate_type == "XOR" {
                    wires[output_wire] = wires[input_wires[0]] ^ wires[input_wires[1]];
                } else {
                    wires[output_wire] = wires[input_wires[0]] & wires[input_wires[1]];
                }
            }
            "INV" => {
                if input_wires.len() != 1 {
                    return Err(FromBristolError::MalformedLine(line_str));
                }
                wires[output_wire] = !wires[input_wires[0]];
            }
            _ => {
                return Err(FromBristolError::UnknownGate(gate_type.to_string()));
            }
        }
    }
    Ok(wires[wires_num - num_output_wires..wires_num].to_vec())
}

#[test]
fn convert_bristol_to_garble() -> Result<(), String> {
    // Compile the Bristol circuit to a Circuit in Garble
    let mult = Circuit::bristol_to_garble(Path::new("bristol_examples/mult64.txt"))
        .map_err(|e| e.prettify())?;

    // Evaluate the circuit with inputs 45678 and 1234 both as Circuit and as Bristol circuit
    let input1_bits: Vec<bool> = (0..64).rev().map(|i| 45678u64 & (1u64 << i) != 0).collect();
    let input2_bits: Vec<bool> = (0..64).rev().map(|i| 1234u64 & (1u64 << i) != 0).collect();

    let output1 = mult.eval(&[input1_bits.clone(), input2_bits.clone()]);
    let output2 = bristol_eval(
        Path::new("bristol_examples/mult64.txt"),
        &[input1_bits.clone(), input2_bits.clone()],
    )
    .map_err(|e| e.prettify())?;
    assert_eq!(output2, output1);

    Ok(())
}

#[test]
fn convert_garble_to_bristol_to_garble() -> Result<(), String> {
    let mult_garble = "
    pub fn main(x: u64, y: u64) -> u64 {
        x * y
    }
    ";
    let mult_garble_prg = compile(mult_garble).map_err(|e| e.prettify(mult_garble))?;

    let mult_bristol = NamedTempFile::new().map_err(|e| e.to_string())?;
    mult_garble_prg
        .circuit
        .clone()
        .unwrap_ssa()
        .format_as_bristol(mult_bristol.path())
        .map_err(|e| e.prettify())?;
    let new_circuit = Circuit::bristol_to_garble(mult_bristol.path()).map_err(|e| e.prettify())?;

    let input1_bits: Vec<bool> = (0..64).rev().map(|i| 45678u64 & (1u64 << i) != 0).collect();
    let input2_bits: Vec<bool> = (0..64).rev().map(|i| 1234u64 & (1u64 << i) != 0).collect();
    // Evaluate the circuit with inputs 45678 and 1234 both as Circuit and as Bristol circuit
    // PANIC_RESULT_SIZE_IN_BITS gets removed from the output as Bristol format does not have panic support
    let output1 = mult_garble_prg
        .circuit
        .unwrap_ssa()
        .eval(&[input1_bits.clone(), input2_bits.clone()])[PANIC_RESULT_SIZE_IN_BITS..]
        .to_vec();
    let output2 = bristol_eval(
        mult_bristol.path(),
        &[input1_bits.clone(), input2_bits.clone()],
    )
    .map_err(|e| e.prettify())?;
    let output3 = new_circuit.eval(&[input1_bits.clone(), input2_bits.clone()]);
    assert_eq!(output2, output1);
    assert_eq!(output3, output2);
    let product: u64 = 45678 * 1234;
    let bits: Vec<bool> = (0..64).rev().map(|i| product & (1u64 << i) != 0).collect();
    assert_eq!(output1, bits);

    Ok(())
}

#[test]
fn convert_garble_to_bristol_output_wire_input() -> Result<(), String> {
    let bad_example = "
    pub fn main(x: u64, y: u64) -> u64 {
        x + 4
    }
    ";
    let bad_compiled = compile(bad_example).map_err(|e| e.prettify(bad_example))?;

    let in_out = NamedTempFile::new().map_err(|e| e.to_string())?;
    let result = bad_compiled
        .circuit
        .unwrap_ssa()
        .format_as_bristol(in_out.path());

    assert!(matches!(result, Err(ToBristolError::OutputWireIsInput)));

    Ok(())
}

#[test]
fn convert_garble_to_bristol_no_directory() -> Result<(), String> {
    let add_garble = "
    pub fn main(x: u64, y: u64) -> u64 {
        x + y
    }
    ";
    let add_garble_prg = compile(add_garble).map_err(|e| e.prettify(add_garble))?;

    let result = add_garble_prg
        .circuit
        .unwrap_ssa()
        .format_as_bristol(Path::new("nonexistent_dir/circuit.txt"));
    assert!(matches!(result, Err(ToBristolError::IoError(_))));

    Ok(())
}

#[test]
fn convert_bristol_to_garble_no_file() -> Result<(), String> {
    // Test with a circuit from a file that does not exist
    let result = Circuit::bristol_to_garble(Path::new("bristol_examples/nonexistent.txt"));
    assert!(matches!(result, Err(FromBristolError::IoError(_))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_malformed_gate_line() -> Result<(), String> {
    // Test with a circuit where the first line is malformed (too many parts)
    let mut mal_gate_line = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(&mut mal_gate_line, "2 5 4").map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(mal_gate_line.path());
    assert!(matches!(result, Err(FromBristolError::MalformedLine(_))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_malformed_input_line() -> Result<(), String> {
    // Test with a circuit where the second (input) line is malformed
    let mut mal_input_line = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut mal_input_line,
        "2 5
        2"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(mal_input_line.path());
    assert!(matches!(result, Err(FromBristolError::MalformedLine(_))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_input_parties() -> Result<(), String> {
    // Test with a circuit where the number of inputs does not match the number of parties in the second line
    let mut input_mismatch = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut input_mismatch,
        "2 5
        2 2 2 3"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(input_mismatch.path());
    assert!(matches!(
        result,
        Err(FromBristolError::InputPartiesMismatch(3, 2))
    ));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_malformed_output_missing() -> Result<(), String> {
    // Test with a circuit where the second (input) line is malformed
    let mut mal_output_line = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut mal_output_line,
        "2 5
        2 2 2
        1"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(mal_output_line.path());
    assert!(matches!(result, Err(FromBristolError::MalformedLine(_))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_output_mismatch() -> Result<(), String> {
    // Test with a circuit where the second (input) line is malformed
    let mut output_mismatch = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut output_mismatch,
        "2 5
        2 2 2
        1 2 3"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(output_mismatch.path());
    assert!(matches!(
        result,
        Err(FromBristolError::OutputCountMismatch(2, 1))
    ));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_too_many_values_to_gate() -> Result<(), String> {
    // Test with a circuit that has a malformed gate line
    let mut mal_gate_many = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut mal_gate_many,
        "2 5
        2 2 2 
        1 2 

        2 1 0 2 4 3 AND"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(mal_gate_many.path());
    assert!(matches!(result, Err(FromBristolError::MalformedLine(_))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_invalid_index() -> Result<(), String> {
    // Test with a circuit that has an invalid wire index
    let mut invalid_index = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut invalid_index,
        "2 5
        2 2 2 
        1 2 

        2 1 0 2 4 AND
        2 1 1 3 5 AND"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(invalid_index.path());
    assert!(matches!(result, Err(FromBristolError::InvalidWireIndex(5))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_wronginput() -> Result<(), String> {
    // Test with a circuit that has a malformed gate line
    let mut wrong_input = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut wrong_input,
        "2 5
        2 2 2 
        1 2 

        1 1 0 2 4 AND"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(wrong_input.path());
    assert!(matches!(result, Err(FromBristolError::MalformedLine(_))));
    Ok(())
}

#[test]
fn convert_bristol_to_garble_unknown_gate() -> Result<(), String> {
    // Test with a circuit that has a malformed gate line with unknown gate type
    let mut unknown_gate = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(
        &mut unknown_gate,
        "2 5
        2 2 2 
        1 2 

        2 1 0 2 4 NAND"
    )
    .map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(unknown_gate.path());
    assert!(matches!(result, Err(FromBristolError::UnknownGate(_))));

    Ok(())
}

#[test]
fn convert_bristol_to_garble_parse_error() -> Result<(), String> {
    // Test with a circuit where the second (input) line is malformed
    let mut parse_error = NamedTempFile::new().map_err(|e| e.to_string())?;
    writeln!(&mut parse_error, "2 a").map_err(|e| e.to_string())?;
    let result = Circuit::bristol_to_garble(parse_error.path());
    assert!(matches!(result, Err(FromBristolError::OtherParseError(_))));
    Ok(())
}
