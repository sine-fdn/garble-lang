# Installation

The easiest way to install the Garble compiler is using `cargo install`:

```
$ cargo install garble_lang --features="bin"
$ garble
Turing-Incomplete Programming Language for Multi-Party Computation with Garbled Circuits

Usage: garble <COMMAND>

Commands:
  run    Run the Garble program with the specified inputs
  check  Check the Garble program for any type errors
  help   Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

If you want to test the Garble compiler with some example programs, the easiest way to do so is to clone the Garble repository and use the programs found in `garble_examples`:

```
$ git clone git@github.com:sine-fdn/garble-lang.git
$ cd garble-lang
$ garble run garble_examples/millionaires.garble.rs --function=main 10000000 10000
Richest::IsA
$ garble run garble_examples/millionaires.garble.rs --function=main 100 5000000
Richest::IsB
$ garble run garble_examples/millionaires.garble.rs --function=main 1000 1000
Richest::Tie
```

If a program cannot be compiled, Garble will report type errors and display the location of the error in the source code:

```
$ garble run garble_examples/error_examples/simple_type_error.garble.rs --function=main 0 true

Type error on line 2:5.
The operands have incompatible types; u32 vs bool:
       | pub fn main(a: u32, b: bool) -> u32 {
   2 > |     a - b
     > |     ^^^^^
       | }
```
