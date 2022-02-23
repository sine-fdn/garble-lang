# A Short Tour of Garble

A minimal Garble program is just a `main` function, with each input conceptually belonging to a different party in the MPC circuit. For example, the following (rather useless) program computes the boolean `and` of two parties:

```rust
fn main(party_a: bool, party_b: bool) -> bool {
    party_a & party_b
}
```

More interesting would be to compute the sum of three parties:

```rust
fn main(a: u32, b: u32, c: u32) -> u32 {
    a + b + c
}
```

Garble will report type errors and display the location of the error in the code if a program cannot be compiled:

```
Type error on line 2:5
--> TypeMismatch((U32, 1:4-1:5), (Bool, 1:8-1:9)):
       | fn main(a: u32, b: bool) -> u32 {
   2 > |     a - b
     > |     ^^^^^
       | }
```

## Control Flow

Let bindings can be used to introduce immutable variables. Since Garble is purely functional, it is not possible to mutate these bindings, but they can be shadowed by bindings of the same name:

```rust
fn main(a: u32, b: u32) -> u32 {
    let sum = a + b;
    let result = sum + sum;
    let result = result + result; // this shadows the existing `result` binding
    result
}
```

Garble supports two forms of control flow: if/else and pattern matching. Both forms are expressions and always return a value. Here's an example of if/else:

```rust
fn main(x: i32) -> i32 {
    if x < 0 {
        -1
    } else if x == 0 {
        0
    } else {
        1
    }
}
```

An here is pattern matching on numbers (see below for examples of pattern matching on tuples and enums):

```rust
fn main(x: i32) -> i32 {
    match x {
        0 => 1,
        x => x,
    }
}
```

Top-level function definitions can be used to split the program into smaller chunks:

```rust
fn main(x: u16) -> u16 {
    inc(x)
}

fn inc(x: u16) -> u16 {
    add(x, 1)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
```


Garble will abort with an error if any of the defined functions are unused:

```
Type error on line 5:2
--> UnusedFn("inc"):
       | fn main(x: u16) -> u16 {
       |     x + 1
   5 > | }
     > |
   6 > |
     > |
   7 > | fn inc(x: u16) -> u16 {
     > | ^^^^^^^^^^^^^^^^^^^^^^^
   8 > |     add(x, 1)
     > | ^^^^^^^^^^^^^
   9 > | }
     > | ^
       |
```

## Primitive Types

Garble supports a number of primitive types: Booleans (`bool`), unsigned integers of different bit lengths (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`) and signed integers of different bit lengths (`i8`, `i16`, `i32`, `i64`, `i128`). If no type is specified, numbers are `i32` by default. Primitive types support the usual logical, bitwise and arithmetic operations:

```rust
fn main(_a: i32, _b: i32) -> i32 {
    let add = 0 + 1;
    let sub = 1 - 1;
    let mul = 2 * 1;
    let div = 2 / 1;
    let rem = 5 % 2;

    let bit_xor = 4 ^ 6;
    let bit_and = 4 & 6;
    let bit_or = 4 | 6;
    let bit_shiftl = 4 << 1;
    let bit_shiftr = 4 >> 1;

    let and = true & false;
    let or = true | false;

    let eq = true == false;
    let neq = true != false;

    let gt = 5 > 4;
    let lt = 4 < 5;
    let gte = 5 >= 4;
    let lte = 4 <= 5;

    let unary_not = !true;
    let unary_minus = -5;
    let unary_bitflip = !5;

    0
}
```

**Please note that Garble currently does not provide any form of overflow detection, errors or panics. Overflows and divide-by-zero errors lead to undefined behavior (but do not crash the program).**

Garble does not do a lot of type coercions, so it is often necessary to either explicitly cast integers to the desired type or declare the type explicitly as part of the literal, with the type directly following the number:

```rust
fn main(a: i32, b: u32) -> i64 {
    let c = -500i64;
    a as i64 + b as i64 + c
}
```

## Collection Types

Several collection types are supported: Fixed-size arrays, ranges, tuples, and enums. Let's look at each of them in turn:

Arrays can be initialized either by explicitly listing all elements (which must have the same type) or by using a 'repeat expression', which repeats a single element a number of times:

```rust
fn main(a: u32, b: u32) -> [u32; 4] {
    let array1 = [a, b, 0u32, 1u32]; // directly listing all elements
    let array2 = [a; 4]; // `a` repeated 4 times
    array2
}
```

Arrays are indexed using `array[index]`, but an index can only be read, never reassigned. Instead, Garble supports a purely function array update syntax using `array.update(index, value)`, which returns a new array with the specified index set to the new value:

```rust
fn main(replacement: i32) -> [i32; 4] {
    let array1 = [10, 20, 30, 40];
    let second_val = array1[1]; // will be `20`
    let array2 = array1.update(1, replacement);
    let second_val = array1[1]; // will still be `20`
    let second_val = array2[1]; // will be equal to `replacement`
    array2
}
```

Ranges are a more convenient notation for arrays of continuous `usize` numbers, they are treated by Garble as arrays and have an array type. The minimum value of a range is inclusive, the maximum value exclusive:

```rust
fn main(_a: i32) -> [usize; 5] {
    10..15 // equal to `[10, 11, 12, 13, 14]`
}
```

Tuples can hold a fixed number of elements of heterogeneous types. Tuple fields are accessed using `tuple.index` (it is not possible to reassign a tuple field):

```rust
fn main(a: i32, b: u64) -> (i32, u64, i128) {
    let sum = (a as i128) + (b as i128);
    let tuple = (a, b, sum);
    let a = tuple.0;
    let b = tuple.1;
    let sum = tuple.2;
    tuple
}
```

Enums must be defined as top-level types before they can be used and are accessed using pattern matching. Patterns must always specify the full enum variant name (`enum_name::variant_name`):

```rust
enum Op {
    Zero,
    Div(u8, u8),
}

enum OpResult {
    DivByZero,
    Ok(u8),
}

fn main(op: Op) -> OpResult {
    match op {
        Op::Zero => OpResult::Ok(0),
        Op::Div(x, 0u8) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
```

Pattern matching is also supported for tuples and range literals (but not arrays). Patterns can be nested:

```rust
fn main(x: (bool, (u8, u8))) -> i32 {
    match x {
        (false, _) => 0,
        (_, (_, 0)) => 1,
        (_, (x, y)) => (x as i32) + (y as i32) + 1,
    }
}
```

If patterns are not exhaustive, Garble will report an error (but currently not report the missing cases):

```
Type error on line 2:5
--> PatternsAreNotExhaustive:
       | fn main(x: (bool, (u8, u8))) -> i32 {
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

## Map / Fold

Garble deliberately only implements a very restricted form of bounded recursion using `.map(...)` and `.fold(...)`, which are only supported on arrays (and ranges). These two constructs borrow Rust's closure syntax, but lambdas / closures / first-class functions are currently not supported anywhere else in the language (and must thus appear directly in `map` / `fold`, they cannot be stored in let bindings):

```rust
fn main(nums: [u8; 5]) -> ([bool; 5], u16) {
    let greater_than_ten = nums.map(|n: u8| -> bool {
        n > 10
    });
    let sum = nums.fold(0, |acc: u16, n: u8| -> u16 {
        acc + (n as u16)
    });
    (greater_than_ten, sum)
}
```
