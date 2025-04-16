# Contributing

While Garble was developed by us at the [SINE Foundation](https://sine.foundation/) for the use in our MPC engine, we would love to see how you end up using Garble and are happy to accept pull requests. Garble is distributed under the MIT license and hosted on GitHub:

[![Github](github-mark.png "Contribute on Github")](https://github.com/sine-fdn/garble-lang)

The Garble compiler is relatively straightforward and turns a program `&str` into a `circuit::Circuit` (or aborts with a scan/parse/type error). The different steps and their modules are as follows (with steps 1-4 happening during compile time, step 5 is optional and happens during run time):

1. [`scan.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/scan.rs) splits a program `&str` into a [`token::Token`](https://github.com/sine-fdn/garble-lang/blob/main/src/token.rs) sequence.
2. [`parse.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/parse.rs) parses a [`token::Token`](https://github.com/sine-fdn/garble-lang/blob/main/src/token.rs) sequence into an untyped [`ast::Program`](https://github.com/sine-fdn/garble-lang/blob/main/src/ast.rs).
3. [`check.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/check.rs) type-checks an untyped [`ast::Program`](https://github.com/sine-fdn/garble-lang/blob/main/src/ast.rs), returning a typed [`ast::Program`](https://github.com/sine-fdn/garble-lang/blob/main/src/ast.rs).
4. [`compile.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/compile.rs) converts a well-typed [`ast::Program`](https://github.com/sine-fdn/garble-lang/blob/main/src/ast.rs) into a [`circuit::Circuit`](https://github.com/sine-fdn/garble-lang/blob/main/src/circuit.rs).
5. [`eval.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/eval.rs) executes a [`circuit::Circuit`](https://github.com/sine-fdn/garble-lang/blob/main/src/circuit.rs) with locally supplied inputs, not using any MPC.

The other modules are less important, but here's a quick overview:

- [`env.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/env.rs) contains a simple data structure that tracks variables in an environment, used during type checking and circuit generation.
- [`lib.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/lib.rs) bundles everything together and contains a couple of high-level convenience functions and wrappers for typed programs and circuits.
- [`literal.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/literal.rs) contains a subset of Garble expressions which can be used as inputs/outputs of a circuit and which support conversion from/to a circuit's bit representation.
- [`main.rs`](https://github.com/sine-fdn/garble-lang/blob/main/src/main.rs) is the optional binary, which can be used to run or type check Garble programs from the command line.

You can also reach us at [vorstand@sine.foundation](mailto:vorstand@sine.foundation).
