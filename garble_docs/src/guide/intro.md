# A Guide to Garble

Garble is a programming language for [MPC](<(https://en.wikipedia.org/wiki/Secure_multi-party_computation)>) that is quite easy to learn and mostly works like Rust, except that it is much simpler and only implements a subset of Rust (without the borrow checker). The following guide introduces the main features of Garble.

A minimal Garble program is a public function (conventionally called `main`), with each input conceptually belonging to a different party in a [MPC Garbled Circuit](https://en.wikipedia.org/wiki/Garbled_circuit). For example, the following program computes the Boolean `and` of two parties:

```rust
pub fn main(party_a: bool, party_b: bool) -> bool {
    party_a & party_b
}
```

The above function is a bit contrived, a more interesting example would be to compute the sum of the inputs of three parties:

```rust
pub fn main(a: u32, b: u32, c: u32) -> u32 {
    a + b + c
}
```
