# Const Parameters

To be able to generate Boolean circuits, Garble programs cannot contain any data structures with a dynamic size, such as a list whose size is only known at run time. Instead, the size of all data structures needs to be known at compile time, which can be quite limiting in practice. For example, two parties might want to compare their data sets without knowing ahead of time how many records each data set contains.

To make this easier, Garble supports `const` parameters, whose size is not yet known while type-checking but will only later be supplied when the program is actually compiled. This makes it possible to develop and check Garble programs without knowing the size of these values in advance. Calling these parameters "constants" might be slightly confusing, because their value is left unspecified before compilation and allows Garble to simulate a restricted form of dynamism, but since Garble is syntactically a subset of Rust and the values are indeed constants during compilation, they are declared using the `const` keyword.

Garble supports Boolean and integer constants, which need to be declared at the top level:

```rust
const MY_CONST: usize = PARTY_0::MY_CONST;

pub fn main(x: u16) -> u16 {
    let array = [2u16; MY_CONST];
    x + array[1]
}
```

Garble also supports taking the `min()` / `max()` of several constants as part of the declaration of a constant, which, for instance, can be useful to set the size of a collection to the size of the biggest collection provided by different parties:

```rust
const MY_CONST: usize = min(PARTY_0::MY_CONST, PARTY_1::MY_CONST);

pub fn main(x: u16) -> u16 {
    let array = [2; MY_CONST];
    x + array[1]
}
```

```rust
const MY_CONST: usize = max(PARTY_0::MY_CONST, PARTY_1::MY_CONST);

pub fn main(x: u16) -> u16 {
    let array = [2; MY_CONST];
    x + array[1]
}
```

> Garble currently does not support type inference in const declarations, which is why you always have to use type suffixes even for simple number literals, e.g. use `2u16` instead of `2`.

Garble programs can be type checked without providing concrete values for the declared constants, but all const values must be provided during compilation, using [`garble_lang::compile_with_constants`](https://docs.rs/garble_lang/latest/garble_lang/fn.compile_with_constants.html). See [MPC Engine Integration](../integration.md) for more details.
