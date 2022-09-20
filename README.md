# Garble Language

Garble is a simple programming language for [Secure Multi-Party Computation](https://en.wikipedia.org/wiki/Secure_multi-party_computation) with [Garbled Circuits](https://en.wikipedia.org/wiki/Garbled_circuit). The circuits generated by Garble specify a _function_, with each input coming from a different party and the output computed collaboratively by all parties in a way that no party learns another party's input. Garble is statically typed, low-level, purely functional and uses a syntax heavily inspired by Rust.

All programs written in Garble are deliberately Turing-incomplete (only supporting bounded recursion), guaranteeing that they can be compiled to circuits using only `AND`, `XOR` and `NOT` gates (without any kind of stateful latches or registers). Here's an example of solving the [Millionaire's Problem](https://en.wikipedia.org/wiki/Yao%27s_Millionaires%27_problem) in Garble:

```rust
// A function for solving Yao's Millionaires' problem:

enum Richest {
    IsA,
    IsB,
    Tie,
}

pub fn main(a: u64, b: u64) -> Richest {
    if a > b {
        Richest::IsA
    } else if b > a {
        Richest::IsB
    } else {
        Richest::Tie
    }
}
```

For more examples, see the [Language Tour](language_tour.md).

## How to Use Garble

The circuits generated by Garble are meant to be executed using a cryptographically secure MPC engine, which is not provided by this crate. Garble is agnostic about the details of the MPC engine and assumes only that the engine executes Garbled Circuits with support for `AND`, `XOR` and `NOT` gates. For local development and testing, Garble supports a direct and unencrypted evaluation of a generated circuit, with all inputs supplied by the local user.

To execute the Millionaire's problem example, first install the `garble` utility, checkout the repository to get the example programs, then run the function inside the repository directory:

```sh
$ cargo install garble_lang
$ git clone git@github.com:sine-fdn/garble-lang.git
$ cd garble-lang
$ garble run garble_examples/millionaires.garble.rs --function=main 10000000u64 10000u64
Richest::IsA
$ garble run garble_examples/millionaires.garble.rs --function=main 100u64 5000000u64
Richest::IsB
$ garble run garble_examples/millionaires.garble.rs --function=main 1000u64 1000u64
Richest::Tie
```

You can also type-check a program without running it by using `garble check` followed by the file name.

(In order to pass inputs which include empty spaces, such as tuples, make sure to encompass them within inverted commas.)

## Architecture of this Repository

The Garble compiler is relatively straightforward and turns a program `&str` into a `circuit::Circuit` (or aborts with a scan/parse/type error). The different steps and their modules are as follows (with steps 1-4 happening during compile time, step 5 during run time):

  1. [`scan.rs`](src/scan.rs) splits a program `&str` into a `token::Token` sequence.
  2. [`parse.rs`](src/parse.rs) parses a `token::Token` sequence into an untyped `ast::Program`.
  3. [`check.rs`](src/check.rs) type-checks an untyped `ast::Program`, returning a typed `ast::Program`.
  4. [`compile.rs`](src/compile.rs) converts a well-typed `ast::Program` into a `circuit::Circuit`.
  5. [`eval.rs`](src/eval.rs) executes a `circuit::Circuit` with locally supplied inputs.
