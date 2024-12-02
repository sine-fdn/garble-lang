# The Garble Programming Language

Garble is a simple programming language for [**Multi-Party Computation**](https://en.wikipedia.org/wiki/Secure_multi-party_computation) with [**Garbled Circuits**](https://en.wikipedia.org/wiki/Garbled_circuit). Garble programs are **compiled to Boolean circuits** and always terminate. Garble is **statically typed, low-level, purely functional** and uses a **Rust-like syntax**. Garble is much simpler than Rust though, making it easy to learn and simple to [integrate](https://sine-fdn.github.io/garble-lang/integration.html) into MPC engines.

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

To learn more about Garble, check out the [website](https://sine-fdn.github.io/garble-lang)
