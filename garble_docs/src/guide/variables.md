# Variables and Mutability

Let bindings can be used to introduce variables, which are immutable by default:

```rust
pub fn main(a: u32, b: u32) -> u32 {
    let sum = a + b;
    let result = sum + sum;
    let result = result + result; // this shadows the existing `result` binding
    result
}
```

The left-hand side of left bindings is not restricted to simple variables, you can also use patterns, as long as they are irrefutable (in other words they always match). Here is an example of how to use let bindings to destructure [tuples and structs](./data_types.md):

```rust
struct FooBar {
    foo: i32,
    bar: (i32, i32),
}

pub fn main(x: (i32, i32)) -> i32 {
    let (a, b) = x;

    let bar = (0, 0);
    let foobar = FooBar { foo: 0, bar };
    let FooBar { bar, .. } = foobar;
    let (y, z) = bar;
    a + y
}
```

Since Garble is purely functional under the hood, it is not possible to have _shared mutable state_: mutable bindings (using `let mut`) are always restricted to the current lexical scope and any values passed to functions are copied by-value, not by-reference:

```rust
pub fn main(x: i32) -> i32 {
    let mut y = 0;
    y = x; // `y` will now be equal to `x`
    let z = inc(y);
    z // is equal to `x + 1`, but `y` is still equal to `x`
}

fn inc(mut a: i32) -> i32 {
    a = a + 1; // the value of `a` is changed only inside this function's scope
    a
}
```

> In contrast to `let`, `let mut` does not support destructuring using patterns. The left-hand side of a `let mut` statement must always be a variable name.

Copying a value on every mutation might sound expensive, but this is actually not the case in a language like Garble that compiles to Boolean gates: Previous values (or more specifically, "wires" with specific Boolean values) can be freely reused, entirely or partially, because there are no memory locations, only gates and their connecting wires.
