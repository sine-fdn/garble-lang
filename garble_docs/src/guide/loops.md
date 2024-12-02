# For Loops and For-Join Loops

Just like Rust, Garble supports for loops that can iterate over a collection of values. In contrast to Rust, Garble also implements a specialized form of these loops to join together sorted collections of records. Let's look at both of these in turn:

## For Loops

Garble supports for loops as the only looping / recursion construct in the language. (Calling a function recursively is a type error.) For loops can only loop over arrays:

```rust
pub fn main(_x: i32) -> i32 {
    let mut sum = 0;
    for i in [2, 4, 6, 8] {
        sum += i
    }
    sum
}
```

Instead of a simple loop variable you can also use destructuring:

```rust
pub fn main(_x: i32) -> i32 {
    let mut sum = 0i32;
    for (a, b) in [(2, 4), (6, 8)] {
        sum += a + b;
    }
    sum
}
```

Arrays in Garble always have a fixed size, Garble does not support data structures of a dynamic length. This is by design, as it disallows any form of unbounded recursion and thus enables the Garble compiler to generate fixed circuits consisting only of Boolean gates. Garble programs are thus computationally equivalent to [LOOP programs](<https://en.wikipedia.org/wiki/LOOP_(programming_language)>), corresponding precisely to the class of _primitive recursive functions_.

## For-Join Loops

Garble has special support for joining together two sorted arrays of tuples, by comparing their first field for equality, which can be useful to combine two data sources coming from different parties similar to a JOIN in SQL. Syntactically, for-join loops are a special case of for loops, using a built-in `join` function instead of an array:

```rust
let rows1 = [(0u8, 10u16), (1u8, 11u16), (2u8, 12u16)];
let rows2 = [(0u8, 5u32, 5u32), (2u8, 6u32, 6u32)];
// The arrays rows1 and rows2 will be joined based on their first field, which is of type u8.
// The tuple (1u8, 11u16) from rows1 is discarded because it cannot be joined with rows2.
for joined in join(rows1, rows2) {
    let ((id1, x), (id2, y, z)) = joined;
    // ...
}
```

Garble automatically joins the arrays in a for-join loop using a [bitonic sorting network](https://en.wikipedia.org/wiki/Bitonic_sorter), more concretely implementing the paper [Private Set Intersection:
Are Garbled Circuits Better than Custom Protocols?](https://www.ndss-symposium.org/wp-content/uploads/2017/09/06_4.pdf) without the shuffle step, which has a circuit complexity of `(m + n) * log(m + n)` instead of `m * n` which would result from joining the arrays using nested loops.

> It is your responsibility to ensure that the **arrays that are joined in the loop must be sorted in ascending order!** Otherwise elements might be discarded or invalid data returned.

For-join loops always join two arrays based on the first field. If you would like to compare more than one field for equality, the easiest way is to transform the sorted array so that the relevant fields are grouped together in a tuple and thus form the first field. Such a transformation will be completely optimized away by the Garble compiler, such as in the following example, which groups together the first two fields, compiled to a circuit with 0 gates:

```rust
pub fn main(arr1: [(u16, u16, u32); 8]) -> [((u16, u16), u32); 8] {
    let mut arr2 = [((0u16, 0u16), 0u32); 8];
    let mut i = 0usize;
    for elem in arr1 {
        let (a, b, c) = elem;
        arr2[i] = ((a, b), c);
        i += 1;
    }
    arr2
}
```

Just like normal for loops, for-join loops support destructuring:

```rust
pub fn main(rows1: [(u8, u16); 3], rows2: [(u8, u16); 3]) -> u16 {
    let mut result = 0u16;
    for ((_, a), (_, b)) in join(rows1, rows2) {
        result += a + b;
    }
    result
}
```
