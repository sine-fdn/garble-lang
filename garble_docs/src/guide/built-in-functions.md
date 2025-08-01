# Built-In Functions

Garble has compiler built-in functions that are currently not expressible in Garble itself.

## Bitonic Join Function
The `bitonic_join` built-in function can be used if a computation should return the actual results of the join (as opposed to looping over the joined elements with [For-Join loop](./loops.md)).

> It is your responsibility to ensure that the **arrays that are joined must be sorted in ascending order!** Otherwise elements might be discarded or invalid data returned.

The return type depends on element type of the joined arrays. If it is **not** a tuple type, the `bitonic_join` function is equivalent to a private set intersection. The result will be an array whose element type is `(bool, T)` where the `bool` indicates if the following element is contained in the intersection or not. If it is `false`, the element will be a dummy element constructed from setting each bit for this type to `0`.

The size of the resulting array will be a [`const` expression](./const.md) of the form `const { SIZE_0 + SIZE_1 - 1usize}`. If you want to return this from a function, the size expression needs to match exactly due to current limitations in the compiler (e.g. `const { SIZE_0 - 1usize + SIZE_1 }` would not work).
```rust
pub fn main(rows1: [[u8; 3]; 5], rows2: [[u8; 3]; 3]) -> [(bool, [u8; 3]); const { 5usize + 3usize - 1usize } ] {
    bitonic_join(rows1, rows2)
}
```

If the element type of both arrays is a tuple, `bitonic_join` functions similar to a For-Join loop where we join on the first element of each tuple and return both tuples in the result. Example:

```rust
pub fn main(rows1: [([u8; 3], u16); 4], rows2: [([u8; 3], u16, u16); 3]) 
    -> [(bool, ([u8; 3], u16), ([u8;3], u16, u16)); const { 4usize + 3usize - 1usize }]
{
    bitonic_join(rows1, rows2)
}
```

If you need to compute a some kind of aggregate over the joined elements, the For-Join loop will be more efficient than looping over the result of `bitonic_join`.

### Internals and Complexity
Similar to the [For-Join](./loops.md) loop, `bitonic_join` is based on a [Bitonic Sorter](https://en.wikipedia.org/wiki/Bitonic_sorter) and the paper [Private Set Intersection:
Are Garbled Circuits Better than Custom Protocols?](https://www.ndss-symposium.org/wp-content/uploads/2017/09/06_4.pdf). Since `bitonic_join` returns all values of the comparison phase, we need to hide the positions of the elements that are part of the intersection. Because the shuffling approaches of the Circuit-PSI paper are incompatible with [Polytune](https://github.com/sine-fdn/polytune), we sort the output of the the comparison phase using a bitonic sorting network. This idea is described in the paper [MPCircuits: Optimized Circuit Generation for Secure Multi-Party Computation](https://ieeexplore.ieee.org/abstract/document/8740831).

Hence, the complexity for two databases of size `n` and `m` is `O((m + n) * log(m + n)^2)` comparisons (note the squared log as opposed to the For-Join loop).
