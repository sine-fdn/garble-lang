# MPC Engine Integration

Integrating Garble into your own MPC engine is pretty straightforward. You have to know how to compile Garble programs, how to encode inputs as Garble literals, and how to understand the circuit format that the Garble compiler produces. Let's look at all of these in more detail:

## Compiling Garble

You can use the [`garble_lang::compile`](https://docs.rs/garble_lang/latest/garble_lang/fn.compile.html) function to compile source code directly into a circuit, which will return an error if there are any parse or type errors. (Or [`garble_lang::compile_with_constants`](https://docs.rs/garble_lang/latest/garble_lang/fn.compile_with_constants.html) in case you are using [`consts`](./guide/const.md) which are only provided after type checking.) It is recommended to `prettify` potential errors so that their location is highlighted in the source code as part of their error message:

```rust
use garble_lang::{compile, literal::Literal, token::UnsignedNumType::U32};

// Compile and type-check a simple program to add the inputs of 3 parties:
let code = "pub fn main(x: u32, y: u32, z: u32) -> u32 { x + y + z }";
let prg = compile(code).map_err(|e| e.prettify(&code)).unwrap();
```

The result is a [`garble_lang::GarbleProgram`](https://docs.rs/garble_lang/latest/garble_lang/struct.GarbleProgram.html), which can be used to access the `circuit` field (if you want to execute the circuit using your own engine), but also exposes type information and allows you to execute the circuit directly (useful for debugging purposes):

```rust
// We can evaluate the circuit directly, useful for testing purposes:
let mut eval = prg.evaluator();
eval.set_u32(2);
eval.set_u32(4);
eval.set_u32(6);
let output = eval.run().map_err(|e| e.prettify(&code)).unwrap();
assert_eq!(u32::try_from(output).map_err(|e| e.prettify(&code)).unwrap(), 2 + 4 + 6);
```

## Encoding Inputs As Literals

If you want to execute a circuit produced by Garble using your own MPC engine, you first need to convert your input arguments into the bit format that the Garble compiler expects. The easiest way to do this is to call `.parse_arg()` or `.parse_literal_arg()` on the `garble_lang::GarbleProgram`, which expects as its first argument the index of the argument in the main function:

```rust
// Inputs arguments can be parsed from strings:
let x = prg.parse_arg(0, "2").unwrap().as_bits();
let y = prg.parse_arg(1, "10").unwrap().as_bits();
let z = prg.parse_arg(2, "100").unwrap().as_bits();
let output = prg.circuit.eval(&[x, y, z]); // use your own MPC engine here instead
let result = prg.parse_output(&output).unwrap();
assert_eq!("112", result.to_string());

// Input arguments can also be constructed directly as literals:
let x = prg.literal_arg(0, Literal::NumUnsigned(2, U32)).unwrap().as_bits();
let y = prg.literal_arg(1, Literal::NumUnsigned(4, U32)).unwrap().as_bits();
let z = prg.literal_arg(2, Literal::NumUnsigned(6, U32)).unwrap().as_bits();
let output = prg.circuit.eval(&[x, y, z]); // use your own MPC engine here instead
let result = prg.parse_output(&output).unwrap();
assert_eq!(Literal::NumUnsigned(12, U32), result);
```

## Garble's Circuit Format

Each [`garble_lang::circuit::Circuit`](https://docs.rs/garble_lang/latest/garble_lang/circuit/struct.Circuit.html) consists of 3 parts:

1. `input_gates`, specifying how many input bits each party must provide
2. `gates`, XOR/AND/NOT intermediate gates (with input gates or intermediate gates as inputs)
3. `output_gates`, specifying which gates should be exposed as outputs (and in which order)

Conceptually, a circuit is a sequence of input or intermediate (XOR/AND/NOT) gates, with all input gates at the beginning of the sequence, followed by all intermediate gates. The index of a gate in the sequence determines its "wire". For example, in a circuit with two input gates (1 bit for party A, 1 bit for party B), followed by three intermediate gates (an XOR of the two input gates, an AND of the two input gates, and an XOR of these two intermediate XOR/AND gates), the input gates would be the wires 0 and 1, the XOR of these two input gates would be specified as `Gate::Xor(0, 1)` and have the wire 2, the AND of the two input gates would be specified as `Gate::And(0, 1)` and have the wire 3, and the XOR of the two intermediate gates would be specified as `Gate::Xor(2, 3)` and have the wire 4:

```text
Input A (Wire 0) ----+----------+
                     |          |
Input B (Wire 1) ----|-----+----|-----+
                     |     |    |     |
                     +-XOR-+    |     |
        (Wire 2) =====> |       |     |
                        |       +-AND-+
        (Wire 3) =======|========> |
                        +---XOR----+
        (Wire 4) ==========> |
```

The input gates of different parties cannot be interleaved: Each party must supply all of their inputs before the next party's inputs can start. Consequently, a circuit with 16 input bits from party A, 8 input bits from party B and 1 input bit from party C would be specified as an `input_gates` field of `vec![16, 8, 1]`.

At least 1 input bit must be specified, not just because a circuit without inputs would not be very useful, but also because the first two intermediate gates of every circuit are constant true and constant false, specified as `Gate::Xor(0, 0)` with wire `n` and `Gate::Not(n)` (and thus depend on the first input bit for their specifications).
