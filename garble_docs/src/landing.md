# The Garble Programming Language

Garble is a simple programming language for [**Multi-Party Computation**](https://en.wikipedia.org/wiki/Secure_multi-party_computation). Garble programs are **compiled to Boolean circuits** and always terminate, making them ideal for [**Garbled Circuits**](https://en.wikipedia.org/wiki/Garbled_circuit). Garble is **statically typed, low-level, purely functional** and uses a **Rust-like syntax**. Garble is much simpler than Rust though, making it easy to learn and simple to [integrate](./integration.md) into MPC engines.

```rust
// A program for solving Yao's Millionaires' problem in Garble:

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

Garble is developed by the [SINE Foundation](https://sine.foundation/) and is [open source](https://github.com/sine-fdn/garble-lang). We developed Garble for our own MPC engine, but you can use Garble in any [MPC engine](./integration.md) that executes Boolean circuits.
