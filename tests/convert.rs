use garble_lang::{
    circuit::PANIC_RESULT_SIZE_IN_BITS,
    compile, compile_bristol_to_circuit, compile_to_bristol,
    convert::{parse_line, ConverterError, FromBristolError},
};

use std::{
    fs::File,
    io::{BufRead, BufReader},
};

/// Evaluates a Bristol format circuit using the given inputs.
fn bristol_eval(path: &str, inputs: &[Vec<bool>]) -> Result<Vec<bool>, ConverterError> {
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

    // Skip the line with the input parts
    lines.next();

    // Parse output parts
    let (output_parts, line_str) = parse_line(lines.next())?;
    if output_parts.len() < 2 {
        return Err(FromBristolError::MalformedLine(line_str).into());
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
            return Err(FromBristolError::MalformedLine(line_str).into());
        }
        let num_inputs: usize = parts[0].parse().map_err(|_| {
            FromBristolError::OtherParseError("Missing number of inputs".to_string())
        })?;
        if parts.len() != num_inputs + 4 {
            return Err(FromBristolError::MalformedLine(line_str).into());
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
                    return Err(FromBristolError::MalformedLine(line_str).into());
                }
                if *gate_type == "XOR" {
                    wires[output_wire] = wires[input_wires[0]] ^ wires[input_wires[1]];
                } else {
                    wires[output_wire] = wires[input_wires[0]] & wires[input_wires[1]];
                }
            }
            "INV" => {
                if input_wires.len() != 1 {
                    return Err(FromBristolError::MalformedLine(line_str).into());
                }
                wires[output_wire] = !wires[input_wires[0]];
            }
            _ => {
                return Err(FromBristolError::UnknownGate(gate_type.to_string()).into());
            }
        }
    }
    Ok(wires[wires_num - num_output_wires..wires_num].to_vec())
}

#[test]
fn convert_bristol_to_garble() -> Result<(), String> {
    // Compile the Bristol circuit to a Circuit in Garble
    let mult =
        compile_bristol_to_circuit("bristol_examples/mult64.txt").map_err(|e| e.prettify(""))?;

    // Evaluate the circuit with inputs 45678 and 1234 both as Circuit and as Bristol circuit
    let input1_bits: Vec<bool> = (0..64).rev().map(|i| 45678u64 & (1u64 << i) != 0).collect();
    let input2_bits: Vec<bool> = (0..64).rev().map(|i| 1234u64 & (1u64 << i) != 0).collect();

    let output1 = mult.eval(&[input1_bits.clone(), input2_bits.clone()]);
    let output2 = bristol_eval(
        "bristol_examples/mult64.txt",
        &[input1_bits.clone(), input2_bits.clone()],
    )
    .map_err(|e| e.prettify())?;
    assert_eq!(output2, output1);

    Ok(())
}

#[test]
fn convert_garble_to_bristol_to_garble() -> Result<(), String> {
    let naive = "
    pub fn main(x: u64, y: u64) -> u64 {
        x * y
    }
    ";
    let compiled = compile(&naive).map_err(|e| e.prettify(naive))?;
    compile_to_bristol(naive, "bristol_examples/circuit.txt").map_err(|e| e.prettify(naive))?;
    let new_circuit =
        compile_bristol_to_circuit("bristol_examples/circuit.txt").map_err(|e| e.prettify(""))?;

    let input1_bits: Vec<bool> = (0..64).rev().map(|i| 45678u64 & (1u64 << i) != 0).collect();
    let input2_bits: Vec<bool> = (0..64).rev().map(|i| 1234u64 & (1u64 << i) != 0).collect();
    // Evaluate the circuit with inputs 45678 and 1234 both as Circuit and as Bristol circuit
    // PANIC_RESULT_SIZE_IN_BITS gets removed from the output as Bristol format does not have panic support
    let output1 = compiled
        .circuit
        .eval(&[input1_bits.clone(), input2_bits.clone()])[PANIC_RESULT_SIZE_IN_BITS..]
        .to_vec();
    let output2 = bristol_eval(
        "bristol_examples/circuit.txt",
        &[input1_bits.clone(), input2_bits.clone()],
    )
    .map_err(|e| e.prettify())?;
    let output3 = new_circuit.eval(&[input1_bits.clone(), input2_bits.clone()]);
    assert_eq!(output2, output1);
    assert_eq!(output3, output2);

    Ok(())
}
