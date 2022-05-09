# A Short Tour of Garble

A minimal Garble program is just a public function, with each input conceptually belonging to a different party in the MPC circuit. For example, the following (rather useless) program computes the boolean `and` of two parties:

```rust
pub fn main(party_a: bool, party_b: bool) -> bool {
    party_a & party_b
}
```

More interesting would be to compute the sum of three parties:

```rust
pub fn main(a: u32, b: u32, c: u32) -> u32 {
    a + b + c
}
```

Garble will report type errors and display the location of the error in the code if a program cannot be compiled:

```shell
$ garble garble_examples/error_examples/simple_type_error.garble.rs main 0u32 true
Type error on line 2:5.
The operands have incompatible types; u32 vs bool:

       | pub fn main(a: u32, b: bool) -> u32 {
   2 > |     a - b
     > |     ^^^^^
       | }
```

## Control Flow

Let bindings can be used to introduce immutable variables. Since Garble is purely functional, it is not possible to mutate these bindings, but they can be shadowed by bindings of the same name:

```rust
pub fn main(a: u32, b: u32) -> u32 {
    let sum = a + b;
    let result = sum + sum;
    let result = result + result; // this shadows the existing `result` binding
    result
}
```

Garble supports two forms of control flow: if/else and pattern matching. Both forms are expressions and always return a value. Here's an example of if/else:

```rust
pub fn main(x: i32) -> i32 {
    if x < 0i32 {
        -1i32
    } else if x == 0i32 {
        0i32
    } else {
        1i32
    }
}
```

And here is pattern matching on numbers (see below for examples of pattern matching on tuples and enums):

```rust
pub fn main(x: i32) -> i32 {
    match x {
        0i32 => 1i32,
        x => x,
    }
}
```

Top-level function definitions can be used to split the program into smaller chunks:

```rust
pub fn main(x: u16) -> u16 {
    inc(x)
}

fn inc(x: u16) -> u16 {
    add(x, 1u16)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
```


Garble will abort with an error if any of the defined functions are unused:

```shell
$ garble garble_examples/error_examples/unused_fn.garble.rs main 0u16
Type error on line 3:2.
Function 'inc' is declared but never used:

       | pub fn main(x: u16) -> u16 {
       |     x + 1u16
   3 > | }
     > |
   4 > |
     > |
   5 > | fn inc(x: u16) -> u16 {
     > | ^^^^^^^^^^^^^^^^^^^^^^^
   6 > |     add(x, 1u16)
     > | ^^^^^^^^^^^^^
   7 > | }
     > | ^
       |
```

## Primitive Types

Garble supports a number of primitive types: Booleans (`bool`), unsigned integers of different bit lengths (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`) and signed integers of different bit lengths (`i8`, `i16`, `i32`, `i64`, `i128`). Note that in contrast to Rust, the type suffix of numbers must always be specified (there is no automatic type coercion), except for tuple/array sizes or indexes (see below). Primitive types support the usual logical, bitwise and arithmetic operations:

```rust
pub fn main(_a: i32, _b: i32) -> i32 {
    let add = 0i32 + 1i32;
    let sub = 1i32 - 1i32;
    let mul = 2i32 * 1i32;
    let div = 2i32 / 1i32;
    let rem = 5i32 % 2i32;

    let bit_xor = 4i32 ^ 6i32;
    let bit_and = 4i32 & 6i32;
    let bit_or = 4i32 | 6i32;
    let bit_shiftl = 4i32 << 1i32;
    let bit_shiftr = 4i32 >> 1i32;

    let and = true & false;
    let or = true | false;

    let eq = true == false;
    let neq = true != false;

    let gt = 5i32 > 4i32;
    let lt = 4i32 < 5i32;
    let gte = 5i32 >= 4i32;
    let lte = 4i32 <= 5i32;

    let unary_not = !true;
    let unary_minus = -5i32;
    let unary_bitflip = !5i32;

    0i32
}
```

Since Garble does not support automatic type coercions, it is often necessary to explicitly cast integers to the desired type:

```rust
pub fn main(a: i32, b: u32) -> i64 {
    let c = -500i64;
    a as i64 + b as i64 + c
}
```

Garble panics if an error occurs, for example due to an integer overflow during an addition:

```shell
$ garble garble_examples/calculator.garble.rs main '(200u8, 200u8)' Op::Add
Panic due to Overflow on line 17:43.

       | pub fn main(values: (u8, u8), op: Op) -> OpResult {
       |     match (op, values) {
  17 > |         (Op::Add, (x, y)) => OpResult::Ok(x + y),
     > |                                           ^^^^^
       |         (Op::Sub, (x, y)) => OpResult::Ok(x - y),
```

## Collection Types

Several collection types are supported: Fixed-size arrays, ranges, tuples, structs and enums. Let's look at each of them in turn:

Arrays can be initialized either by explicitly listing all elements (which must have the same type) or by using a 'repeat expression', which repeats a single element a number of times. Note that the size of an array is specified without any type suffix (`4`, not `4usize`):

```rust
pub fn main(a: u32, b: u32) -> [u32; 4] {
    let array1 = [a, b, 0u32, 1u32]; // directly listing all elements
    let array2 = [a; 4]; // `a` repeated 4 times
    array2
}
```

Arrays are indexed using `array[index]` (with a literal index being written without type suffix), but an index can only be read, never reassigned. Instead, Garble supports a purely functional array update syntax using `array.update(index, value)`, which returns a new array with the specified index set to the new value:

```rust
pub fn main(replacement: i32) -> [i32; 4] {
    let array1 = [10i32, 20i32, 30i32, 40i32];
    let second_val = array1[1]; // will be `20i32`
    let array2 = array1.update(1, replacement);
    let second_val = array1[1]; // will still be `20i32`
    let second_val = array2[1]; // will be equal to the value of `replacement`
    array2
}
```

Ranges are a more convenient notation for arrays of continuous numbers. They are treated by Garble as arrays and have an array type. The minimum value of a range is inclusive, the maximum value exclusive:

```rust
pub fn main(_a: i32) -> [usize; 5] {
    10i32..15i32 // equivalent to `[10i32, 11i32, 12i32, 13i32, 14i32]`
}
```

Tuples can hold a fixed number of elements of heterogeneous types. Tuple fields are accessed using `.` followed by an index (without type suffix) or using let-destructuring (tuples are immutable, so it is not possible to reassign a tuple field):

```rust
pub fn main(a: i32, b: u64) -> (i32, u64, i128) {
    let sum = (a as i128) + (b as i128);
    let tuple = (a, b, sum);
    let a = tuple.0;
    let b = tuple.1;
    let sum = tuple.2;
    let (a, b, sum) = tuple;
    tuple
}
```

Structs must be declared as top-level types before they can be used. Note that unlike in Rust, only record-style structs (with named fields) are supported:

```rust
struct FooBar {
    foo: i32,
    bar: i32,
}

pub fn main(x: i32) -> i32 {
    let foobar = FooBar { foo: x, bar: 2i32 };
    foobar.bar
}
```

Similar to structs, enums must be declared as top-level types before they can be used and are accessed using pattern matching. Unlike in Rust, patterns must always specify the full enum variant name (e.g. `EnumName::VariantName`):

```rust
enum Op {
    Zero,
    Div(u8, u8),
}

enum OpResult {
    DivByZero,
    Ok(u8),
}

pub fn main(op: Op) -> OpResult {
    match op {
        Op::Zero => OpResult::Ok(0u8),
        Op::Div(x, 0u8) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
```

Pattern matching is also supported for tuples and range literals (but not arrays). Patterns can be nested:

```rust
fn main(x: (bool, (u8, u8))) -> i32 {
    match x {
        (false, _) => 0i32,
        (_, (_, 0u8)) => 1i32,
        (_, (x, y)) => (x as i32) + (y as i32) + 1i32,
    }
}
```

Garble also supports inclusive-end ranges in patterns (but only there, not yet as array literals), using `..=` instead of `..`:

```rust
pub fn main(x: u8) -> u8 {
    match x {
        0u8..10u8 => 1u8,
        10u8 => 2u8,
        11u8 => 2u8,
        13u8 => 2u8,
        12u8..100u8 => 2u8,
        100u8..=255u8 => 3u8,
    }
}
```

If patterns are not exhaustive, Garble will report the missing cases:

```shell
$ garble garble_examples/error_examples/non_exhaustive_patterns.garble.rs main '(true, (0u8, 0u8))'
Type error on line 2:5.
The patterns are not exhaustive. Missing cases:

  (true, (1..256, 1..256))

...in expression:

       | pub fn main(x: (bool, (u8, u8))) -> i32 {
   2 > |     match x {
     > |     ^^^^^^^^^
   3 > |         (false, _) => 0u8,
     > | ^^^^^^^^^^^^^^^^^^^^^^^^^^
   4 > |         (_, (_, 0u8)) => 1u8,
     > | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   5 > |         (_, (0u8, y)) => 2u8,
     > | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   6 > |     }
     > | ^^^^^
       | }
```

## Map / Fold

Garble deliberately only implements a very restricted form of bounded recursion using `.map(...)` and `.fold(...)`, which are only supported on arrays (and ranges):

```rust
fn main(nums: [u8; 5]) -> ([bool; 5], u16) {
    let greater_than_ten = nums.map(|n: u8| -> bool {
        n > 10u8
    });
    let sum = nums.fold(0u16, |acc: u16, n: u8| -> u16 {
        acc + (n as u16)
    });
    (greater_than_ten, sum)
}
```

`map`/`fold` borrow Rust's closure syntax, but lambdas / closures / first-class functions are currently not supported anywhere else in the language (and must thus appear directly in `map` / `fold`, they cannot be stored in let bindings, for example).
