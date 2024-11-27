# If/Else and Pattern Matching

Garble supports two forms of conditional control flow, if/else and pattern matching, which are both expressions and always return a value. Here's an example of if/else:

```rust
pub fn main(x: i32) -> i32 {
    if x < 0 {
        -1
    } else if x == 0 {
        0
    } else {
        1
    }
}
```

Here is an example of pattern matching on numbers:

```rust
pub fn main(x: i32) -> i32 {
    match x {
        0 => 1,
        x => x,
    }
}
```

Pattern matching is also supported for enums, structs, tuples and range literals (but not for arbitrary arrays), see the description of [data types](./data_types.md) for more details. Here's how to match on an enum:

```rust
pub fn main(op: Op) -> OpResult {
    match op {
        Op::Zero => OpResult::Ok(0),
        Op::Div(x, 0) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
```

As in Rust, patterns can be nested:

```rust
fn main(x: (bool, (u8, u8))) -> i32 {
    match x {
        (false, _) => 0,
        (_, (_, 0)) => 1,
        (_, (x, y)) => (x as i32) + (y as i32) + 1,
    }
}
```

Garble also supports inclusive-end ranges in patterns (but only in patterns, not as array literals), using `..=` instead of `..`:

```rust
pub fn main(x: u8) -> u8 {
    match x {
        0..10 => 1,
        10 => 2,
        11 => 2,
        13 => 2,
        12..100 => 2,
        100..=255 => 3,
    }
}
```

Garble supports Rust's `..` shorthand in structs, to ignore all remaining fields:

```rust
struct FooBar {
    foo: i32,
    bar: i32,
}

pub fn main(x: (i32, i32)) -> i32 {
    let (foo, bar) = x;
    let foobar = FooBar { foo, bar };
    match foobar {
        FooBar { foo: 0, .. } => 1,
        FooBar { foo, .. } => foo,
    }
}
```

If patterns are not exhaustive, Garble will report the missing cases:

```shell
$ garble run garble_examples/error_examples/non_exhaustive_patterns.garble.rs --function=main '(true, (0, 0))'
Type error on line 2:5.
The patterns are not exhaustive. Missing cases:

  (true, (1u8..=255u8, 1u8..=255u8))

...in expression:
       | pub fn main(x: (bool, (u8, u8))) -> i32 {
   2 > |     match x {
     > |     ^^^^^^^^^
   3 > |         (false, _) => 0,
     > | ^^^^^^^^^^^^^^^^^^^^^^^^
   4 > |         (_, (_, 0)) => 1,
     > | ^^^^^^^^^^^^^^^^^^^^^^^^^
   5 > |         (_, (0, y)) => 2,
     > | ^^^^^^^^^^^^^^^^^^^^^^^^^
   6 > |     }
     > | ^^^^^
       | }
```
