---
title: "Garble Language"
---

# Garble — A Language for Multi-Party Computation

Garble is a Turing-incomplete Programming Language for Multi-Party Computation (MPC) with Garbled Circuits. Garble can be compiled to Boolean (AND, XOR and NOT) gates and always terminates. Garble's syntax is a subset of Rust and all of its concepts will be familiar to Rust programmers. Garble is much simpler though, making it easy to learn and integrate into MPC engines.

Here's a taste of Garble:

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
