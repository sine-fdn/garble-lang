# A Guide to Garble

Garble is a programming language for [MPC](https://en.wikipedia.org/wiki/Secure_multi-party_computation) that is quite easy to learn and mostly works like Rust, except that it is much simpler and only implements a subset of Rust (without the borrow checker). The following guide introduces the main features of Garble.

A minimal Garble program is a public function (conventionally called `main`), with each argument coming from a different party in an MPC protocol based on Boolean circuits, e.g. [Garbled Circuits](https://en.wikipedia.org/wiki/Garbled_circuit). For example, the following program computes the Boolean `and` of two parties:

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

It is also possible to use a single array as the argument of the main function, Garble will then assume that each array element is coming from a different party. So we could also write the above as:

```rust
pub fn main(parties: [u32; 3]) -> u32 {
    parties[0] + parties[1] + parties[2]
}
```
