# Functions

Garble programs are a collection of pure functions. There are no side effects such as printing output or doing any other form of IO. Functions that are meant to be invoked as the entry points of multi-party computations must be marked public by using the `pub` modifier. Non-`pub` top-level function definitions can be used to split the program into smaller chunks:

```rust
pub fn main(x: u16) -> u16 {
    inc(x)
}

fn inc(x: u16) -> u16 {
    add(x, 1)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
```

Garble will abort with an error if any of the non-`pub` defined functions are unused:

```
$ garble run garble_examples/error_examples/unused_fn.garble.rs --function=main 0
Type error on line 3:2.
Function 'inc' is declared but never used:

       | pub fn main(x: u16) -> u16 {
       |     x + 1
   3 > | }
     > |
   4 > |
     > |
   5 > | fn inc(x: u16) -> u16 {
     > | ^^^^^^^^^^^^^^^^^^^^^^^
   6 > |     add(x, 1)
     > | ^^^^^^^^^^^^^
   7 > | }
     > | ^
       |
```

Garble panics if an error occurs, for example if an integer overflows during an addition:

```
$ garble run garble_examples/calculator.garble.rs --function=main '(200, 200)' Op::Add
Panic due to Overflow on line 17:43.

       | pub fn main(values: (u8, u8), op: Op) -> OpResult {
       |     match (op, values) {
  17 > |         (Op::Add, (x, y)) => OpResult::Ok(x + y),
     > |                                           ^^^^^
       |         (Op::Sub, (x, y)) => OpResult::Ok(x - y),
```

Garble will also panic on integer overflows caused by other arithmetic operations (such as subtraction and multiplication), divisions by zero, and out-of-bounds array indexing.

> Circuit logic for panics is always compiled into the final circuit (and includes the line and column number of the code that caused the panic), **it is your responsibility to ensure that no sensitive information can be leaked by causing a panic**.

Just like Rust, Garble supports both `//` and (nested) `/* */` comments:

```rust
/*
fn unused_fn(x: ...) -> ... {
    /* nested block comment */
    // normal comment within block comment
}
*/
pub fn main(x: u16) -> u16 {
    // comment including '/*'
    x + /* ... */ 1
}
```
