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

Garble programs are a collection of pure functions (there are no side effects such as printing output or doing any other form of IO). Functions that are meant to be invoked as the entry points of multi-party computations must be marked public by using the `pub` modifier. Non-`pub` top-level function definitions can be used to split the program into smaller chunks:

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

Garble will abort with an error if any of the non-`pub` defined functions are unused:

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

## Control Flow

Let bindings can be used to introduce variables, which are immutable by default:

```rust
pub fn main(a: u32, b: u32) -> u32 {
    let sum = a + b;
    let result = sum + sum;
    let result = result + result; // this shadows the existing `result` binding
    result
}
```

Since Garble is purely functional under the hood, it is not possible to have _shared mutable state_: mutable bindings (using `let mut`) are always restricted to the current lexical scope and any values passed to functions are copied by-value, not by-reference:

```rust
pub fn main(x: i32) -> i32 {
    let mut y = 0i32;
    y = x; // `y` will now be equal to `x`
    let z = inc(y);
    z // is equal to `x + 1`, but `y` is still equal to `x`
}

fn inc(mut a: i32) -> i32 {
    a = a + 1; // the value of `a` is changed only inside this function's scope
    a
}
```

Garble supports two forms of conditional control flow: if/else and pattern matching. Both forms are expressions and always return a value. Here's an example of if/else:

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

Here is an example of pattern matching on numbers (see below for examples of pattern matching on collections):

```rust
pub fn main(x: i32) -> i32 {
    match x {
        0i32 => 1i32,
        x => x,
    }
}
```

Garble supports for-each loops as the only looping / recursion construct in the language. Note that for-each loops can only loop over _fixed-size_ arrays. This is by design, as it disallows any form of unbounded recursion and thus enables the Garble compiler to generate fixed circuits consisting only of boolean gates. Garble programs are thus computationally equivalent to [LOOP programs](https://en.wikipedia.org/wiki/LOOP_(programming_language)) and capture the class of _primitive recursive functions_.

```rust
pub fn main(_x: i32) -> i32 {
    let mut sum = 0i32;
    for i in [2i32, 4i32, 6i32, 8i32] {
        sum = sum + i
    }
    sum
}
```

## Primitive Types

Garble supports a number of primitive types: Booleans (`bool`), unsigned integers of different bit lengths (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`) and signed integers of different bit lengths (`i8`, `i16`, `i32`, `i64`, `i128`). Note that in contrast to Rust, the type suffix of a number must always be specified (and there is no automatic type coercion), except for tuple/array sizes or indexes (see below). Primitive types support the usual logical, bitwise and arithmetic operations:

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

## Panics

Garble panics if an error occurs, for example if an integer overflows during an addition:

```shell
$ garble garble_examples/calculator.garble.rs main '(200u8, 200u8)' Op::Add
Panic due to Overflow on line 17:43.

       | pub fn main(values: (u8, u8), op: Op) -> OpResult {
       |     match (op, values) {
  17 > |         (Op::Add, (x, y)) => OpResult::Ok(x + y),
     > |                                           ^^^^^
       |         (Op::Sub, (x, y)) => OpResult::Ok(x - y),
```

Garble will also panic on integer overflows caused by other arithmetic operations (such as subtraction and multiplication), divisions by zero, and out-of-bounds array indexing.

*Circuit logic for panics is always compiled into the final circuit (and includes the line and column number of the code that caused the panic), it is your responsibility to ensure that no sensitive information can be leaked by deliberately causing a panic.*

## Collection Types

Several collection types are supported: Fixed-size arrays, ranges, tuples, structs and enums. Let's look at each of them in turn:

### Arrays and Ranges

Arrays can be initialized either by explicitly listing all elements (which must have the same type) or by using a 'repeat expression', which repeats a single element a number of times. Note that the size of an array is specified without any type suffix (`4`, not `4usize`):

```rust
pub fn main(a: u32, b: u32) -> [u32; 4] {
    let array1 = [a, b, 0u32, 1u32]; // directly listing all elements
    let array2 = [a; 4]; // `a` repeated 4 times
    array2
}
```

Arrays are indexed using `array[index]` (with a literal index being written without type suffix). A single element can be reassigned if the whole array has been declared as mutable by `let mut`. Note that whole arrays are copied by value, so that mutating a single index only changes one single array, never any of its copies (which might sound inefficient, but does not incur any performance penalty in a purely functional circuit using only boolean gates).

```rust
pub fn main(replacement: i32) -> [i32; 4] {
    let mut array1 = [10i32, 20i32, 30i32, 40i32];
    let second_val = array1[1]; // will be `20i32`
    let mut array2 = array1;
    array2[1] = replacement;
    let second_val1 = array1[1]; // still `20i32`
    let second_val2 = array2[1]; // equal to the value of `replacement`
    array2
}
```

Ranges are a more convenient notation for arrays of continuous numbers. They are treated by Garble as arrays and have an array type. The minimum value of a range is inclusive, the maximum value exclusive:

```rust
pub fn main(_a: i32) -> [usize; 5] {
    10i32..15i32 // equivalent to `[10i32, 11i32, 12i32, 13i32, 14i32]`
}
```

### Tuples

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

### Structs

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

Similar to Rust, Garble offers a bit of syntactic sugar for dealing with structs. If the value of a field is a variable with the same name as the field, the value can be omitted (writing `Foo { bar }` instead of `Foo { bar: bar }`), both in patterns and in struct literals. Additionally, a subset of the fields of a struct can be matched by ignoring the remaining fields using `..`:

```rust
struct FooBar {
    foo: i32,
    bar: i32,
}

pub fn main(x: (i32, i32)) -> i32 {
    let (foo, bar) = x;
    let foobar = FooBar { foo, bar };
    match foobar {
        FooBar { foo: 0i32, .. } => 1i32,
        FooBar { foo, .. } => foo,
    }
}
```

Note that just like tuples, structs are immutable, so it is not possible to reassign a struct field.

### Enums

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

Pattern matching is also supported for structs, tuples and range literals (but not arrays). Patterns can be nested:

```rust
fn main(x: (bool, (u8, u8))) -> i32 {
    match x {
        (false, _) => 0i32,
        (_, (_, 0u8)) => 1i32,
        (_, (x, y)) => (x as i32) + (y as i32) + 1i32,
    }
}
```

Garble also supports inclusive-end ranges in patterns (but only in patterns, not as array literals), using `..=` instead of `..`:

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

## Mental Model of Garble Programs

It is important to keep in mind that Garble programs are boolean *circuits*, which consist of a graph of logic gates, not a sequentially executed program of instructions on a von Neumann architecture with main memory and CPU. This has deep consequences for the programming style that leads to efficient Garble programs, with programs that would be efficient in "normal" programming languages resulting in highly inefficient circuits and vice versa.

One example has already briefly been mentioned: Copying whole arrays in Garble is essentially free, because arrays (and their elements) are just a collection of output wires from a bunch of boolean logic gates. Duplicating these wires does not increase the complexity of the circuit, because no additional logic gates are required.

Replacing the element at a *constant* index in an array with a new value is equally cheap, because the Garble compiler can just duplicate the output wires of all the other elements and only has to use the wires of the replacement element where previously the old element was being used. In contrast, replacing the element at a *non-constant* index (i.e. an index that depends on a runtime value) is a much more expensive operation in a boolean circuit than it would be on a normal computer, because the Garble compiler has to generate a nested multiplexer circuit.

Here's an additional example: Let's assume that you want to implement an MPC function that on each invocation adds a value into a (fixed-size) collection of values, overwriting previous values if the buffer is full. In most languages, this could be easily done using a ring buffer and the same is possible in Garble:

```rust
pub fn main(mut arr: [u16; 500], i: usize, x: u16) -> [u16; 500] {
    arr[i % 500usize] = x;
    arr
}
```

However, Garble has no way of knowing that the above function is meant to implement a ring buffer and that the value of `i` will only be incremented in steps of 1 between each invocation. From the perspective of the compiler, the above code requires an array access at an arbitrary location, which requires the Garble compiler to generate a nested multiplexer circuit.

Instead of passing the parameter `i` as an input, we could also "shift" the whole array by 1 element, constructing a new array in the process. This would require a lot of copying in other languages, but is much more performant in Garble:

```rust
pub fn main(arr: [u16; 500], x: u16) -> [u16; 500] {
    let mut arr2 = [0u16; 500];
    arr2[0] = x;
    for i in 1usize..500usize {
        arr2[i] = arr[i - 1usize]
    }
    arr2
}
```

The difference in circuit size is staggering: While the first version (with `i` as an input parameter) is compiled to a circuit with more than 700,000 non-input gates, the second version (which shifts the entire array by one element) uses only 2 non-input gates (because the program is effectively a static transformation from input to output).

Such an example is admittedly a bit contrived, especially since an entirely static transformation such as the shifted-array version above does not make much sense in an MPC-context, where inputs should be kept hidden. But it does highlight how unintuitive the computational model of pure boolean circuits can be from the perspective of a load-and-store architecture with main memory and CPU.

It can be helpful to think of Garble programs as being executed on a computer with infinite memory, free copying and no garbage collection: Nothing ever goes out of scope, it is therefore trivial to reuse old values. But any form of branching or looping needs to be compiled into a circuit where each possible branch or loop invocation is "unrolled" and requires its own dedicated logic gates. In normal programming languages, looping a few additional times does not increase the program size, but in Garble programs additional gates are necessary. The size of Garble programs therefore reflects the *worst case* algorithm performance: While normal programming languages can return early and will often require much less time in the best or average case than in the worst case, the evaluation of Garble programs will always take constant time, because the full circuit must always be evaluated.
