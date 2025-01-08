# Circuits and Termination

Garble programs are Boolean _circuits_ consisting of a graph of logic gates, not sequentially executed programs of instructions on a von Neumann architecture with main memory and CPU. This has deep consequences for the programming style that leads to efficient Garble programs, with programs that would be efficient in "normal" programming languages resulting in highly inefficient circuits and vice versa.

## Copying is Free

One example has already been mentioned in the context of [arrays](./guide/data_types.md#arrays-and-ranges): Copying whole arrays in Garble is essentially free, because arrays (and their elements) are just a collection of output wires from a bunch of Boolean logic gates. Duplicating these wires does not increase the complexity of the circuit, because no additional logic gates are required.

Replacing the element at a _constant_ index in an array with a new value is equally cheap, because the Garble compiler can just duplicate the output wires of all the other elements and only has to use the wires of the replacement element where previously the old element was being used. In contrast, replacing the element at a _non-constant_ index (i.e. an index that depends on a runtime value) is a much more expensive operation in a Boolean circuit than it would be on a normal computer, because the Garble compiler has to generate a nested multiplexer circuit.

The following program seems to do a lot of work, but is actually just re-arranging the bits in an array, turning each element from a tuple of three values into a nested tuple. Garble optimizes the actual loop away, resulting in a program with 0 AND gates:

```rust
pub fn main(arr1: [(u16, u16, u32); 8]) -> [((u16, u16), u32); 8] {
    let mut arr2 = [((0u16, 0u16), 0u32); 8];
    let mut i = 0usize;
    for elem in arr1 {
        let (a, b, c) = elem;
        arr2[i] = ((a, b), c);
        i = i + 1usize;
    }
    arr2
}
```

## Branching is Expensive

Here's an additional example: Let's assume that you want to implement an MPC function that on each invocation adds a value into a (fixed-size) collection of values, overwriting previous values if the buffer is full. In most languages, this could be easily done using a ring buffer and the same is possible in Garble:

```rust
pub fn main(mut arr: [u16; 500], i: usize, x: u16) -> [u16; 500] {
    arr[i % 500] = x;
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

The difference in circuit size is extreme: While the first version (with `i` as an input parameter) is compiled to a circuit with more than 700,000 non-input gates, the second version (which shifts the entire array by one element) uses only 2 non-input gates (because the program is effectively a static transformation from input to output).

Such an example might be a bit contrived, since it is possible to infer the inputs of both parties (except for the element that is dropped from the array) from the output of the above function, defeating the purpose of MPC, which is to keep each party's input private. But it does highlight how unintuitive the computational model of pure Boolean circuits can be from the perspective of a load-and-store architecture with main memory and CPU.

## Garble's Computational Model

It can be helpful to think of Garble programs as being executed on a computer with infinite memory, free copying and no garbage collection: Nothing ever goes out of scope, it is therefore trivial to reuse old values. But any form of branching or looping needs to be compiled into a circuit where each possible branch or loop invocation is "unrolled" and requires its own dedicated logic gates. In normal programming languages, looping a few additional times does not increase the program size, but in Garble programs additional gates are necessary. The size of Garble programs therefore reflects the _worst case_ algorithm performance: While normal programming languages can return early and will often require much less time in the best or average case than in the worst case, the evaluation of Garble programs will always take constant time, because the full circuit must always be evaluated.
