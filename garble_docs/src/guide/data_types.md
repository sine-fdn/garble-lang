# Data Types

Garble supports several primitive types: Booleans (`bool`), unsigned integers of different bit lengths (`u8`, `u16`, `u32`, `u64`, `usize`) and signed integers of different bit lengths (`i8`, `i16`, `i32`, `i64`). Note that in contrast to Rust, the type suffix of a number must sometimes be specified because Garble only supports a limited form of type inference for numbers. If no type suffix is specified and Garble cannot figure out the type, `i32` will be used by default.

Primitive types support the usual logical, bitwise and arithmetic operations:

```rust
pub fn main(_a: i32, _b: i32) -> () {
    let add = 0 + 1;
    let sub = 1 - 1;
    let mul = 2 * 1;
    let div = 2 / 1;
    let rem = 5 % 2;

    let bit_xor = 4u32 ^ 6;
    let bit_and = 4u32 & 6;
    let bit_or = 4u32 | 6;
    let bit_shiftl = 4u32 << 1;
    let bit_shiftr = 4u32 >> 1;

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
    let unary_bitflip = !5u32;
}
```

Just like Rust, Garble supports short forms that combine assignment and operators, e.g. `a += 1` as a short form for `a = a + 1`:

```rust
pub fn main(_a: i32, _b: i32) -> () {
    let mut x = 0i32;
    x += 5;
    x -= 3;
    x *= 3;
    x /= 2;
    x %= 1;

    let mut x = 0u32;
    x ^= 4;
    x &= 3;
    x |= 2;
    x <<= 1;
    x >>= 1;

    let mut b = true;
    b ^= true;
    b &= true;
    b |= true;
}
```

Since Garble does not support automatic type coercions, it is often necessary to explicitly cast integers to the desired type:

```rust
pub fn main(a: i32, b: u32) -> i64 {
    let c = -500i64;
    a as i64 + b as i64 + c
}
```

Several collection types are supported: Fixed-size arrays, ranges, tuples, structs and enums. In contrast to Rust, all collection types in Garble support equality comparison (`==`) out of the box.

## Arrays and Ranges

Arrays can be initialized either by explicitly listing all elements (which must have the same type) or by using a 'repeat expression', which repeats a single element a number of times.

```rust
pub fn main(a: u32, b: u32) -> [u32; 4] {
    let array1 = [a, b, 0u32, 1u32]; // directly listing all elements
    let array2 = [a; 4]; // `a` repeated 4 times
    array2
}
```

Arrays are indexed using `array[index]`. An element can be reassigned if the whole array has been declared as mutable by `let mut`. Each new let binding, no matter whether immutable or mutable, always copies the full array: As a result, mutating a single index only affects a single variable, never any other "copies" of the array. This might sound inefficient, but does not incur any performance penalty in a purely functional circuit using only boolean gates. Consequently, there is no shared mutable state in Garble:

```rust
pub fn main(replacement: i32) -> [i32; 4] {
    let mut array1 = [10, 20, 30, 40];
    let second_val = array1[1]; // will be `20`
    let mut array2 = array1;
    array2[1] = replacement;
    let second_val1 = array1[1]; // still `20`
    let second_val2 = array2[1]; // equal to the value of `replacement`
    array2
}
```

Ranges are a more convenient notation for arrays of continuous numbers. They are treated by Garble as arrays and have an array type. The minimum value of a range is inclusive, the maximum value exclusive:

```rust
pub fn main(_a: i32) -> [i32; 5] {
    10..15 // equivalent to `[10, 11, 12, 13, 14]`
}
```

## Tuples

Tuples can hold a fixed number of elements of heterogeneous types. Tuple fields are accessed using `.` followed by an index (without type suffix) or using let-destructuring (tuples are immutable, so it is not possible to reassign a tuple field):

```rust
pub fn main(a: i32, b: u64) -> (i32, u64, i64) {
    let sum = (a as i64) + (b as i64);
    let tuple = (a, b, sum);
    let a = tuple.0;
    let b = tuple.1;
    let sum = tuple.2;
    let (a, b, sum) = tuple;
    tuple
}
```

## Structs

Structs must be declared as top-level types before they can be used. Note that unlike in Rust, only record-style structs (with named fields) are supported:

```rust
struct FooBar {
    foo: i32,
    bar: i32,
}

pub fn main(x: i32) -> i32 {
    let foobar = FooBar { foo: x, bar: 2 };
    foobar.bar
}
```

Similar to Rust, Garble offers syntactic sugar for dealing with structs. If the value of a field is a variable with the same name as the field, the value can be omitted (writing `Foo { bar }` instead of `Foo { bar: bar }`), both in patterns and in struct literals. Additionally, a subset of the fields of a struct can be matched by ignoring the remaining fields using `..`:

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

Just like tuples, structs are immutable, so it is not possible to reassign a struct field.

## Enums

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
```

Fields on an enum can be accessed using [pattern matching](./control_flow.md):

```rust
pub fn main(op: Op) -> OpResult {
    match op {
        Op::Zero => OpResult::Ok(0),
        Op::Div(x, 0) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
```
