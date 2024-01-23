use garble_lang::compile;

#[test]
fn optimize_or() -> Result<(), String> {
    let unoptimized = "
pub fn main(x: bool) -> bool {
    x | true
}
";
    let optimized = "
pub fn main(_x: bool) -> bool {
    true
}
";
    let unoptimized = compile(unoptimized).map_err(|e| e.prettify(unoptimized))?;
    let optimized = compile(optimized).map_err(|e| e.prettify(optimized))?;

    assert_eq!(
        unoptimized.circuit.gates.len(),
        optimized.circuit.gates.len()
    );
    Ok(())
}

#[test]
fn optimize_const_add() -> Result<(), String> {
    let unoptimized = "
pub fn main(_x: i32) -> i32 {
    1i32 + 2i32 + 3i32 + 4i32
}
";
    let optimized = "
pub fn main(_x: i32) -> i32 {
    10i32
}
";
    let unoptimized = compile(unoptimized).map_err(|e| e.prettify(unoptimized))?;
    let optimized = compile(optimized).map_err(|e| e.prettify(optimized))?;

    assert_eq!(
        unoptimized.circuit.gates.len(),
        optimized.circuit.gates.len()
    );
    Ok(())
}

#[test]
fn optimize_same_expr() -> Result<(), String> {
    let unoptimized = "
pub fn main(b: bool, x: i32) -> bool {
    if b { x < x } else { x < x }
}
";
    let optimized = "
pub fn main(b: bool, x: i32) -> bool {
    let y = x < x;
    if b { y } else { y }
}
";
    let unoptimized = compile(unoptimized).map_err(|e| e.prettify(unoptimized))?;
    let optimized = compile(optimized).map_err(|e| e.prettify(optimized))?;
    assert_eq!(
        unoptimized.circuit.gates.len(),
        optimized.circuit.gates.len()
    );
    Ok(())
}

#[test]
fn optimize_not_equivalence() -> Result<(), String> {
    let unoptimized = "
pub fn main(b: bool) -> bool {
    !!b
}
";
    let optimized = "
pub fn main(b: bool) -> bool {
    b
}
";
    let unoptimized = compile(unoptimized).map_err(|e| e.prettify(unoptimized))?;
    let optimized = compile(optimized).map_err(|e| e.prettify(optimized))?;
    assert_eq!(
        unoptimized.circuit.gates.len(),
        optimized.circuit.gates.len()
    );
    Ok(())
}

#[test]
fn optimize_bit_shifts1() -> Result<(), String> {
    let unoptimized = "
pub fn main(arr1: [u32; 2], arr2: [u32; 2], choice: bool) -> [u8; 8] {
    let arr = if choice { arr1 } else { arr2 };
    [
        (arr[0] >> 24u8) as u8,
        (arr[0] >> 16u8) as u8,
        (arr[0] >> 8u8) as u8,
        arr[0] as u8,
        (arr[1] >> 24u8) as u8,
        (arr[1] >> 16u8) as u8,
        (arr[1] >> 8u8) as u8,
        arr[1] as u8,
    ]
}
";
    let optimized = "
pub fn main(arr1: [u8; 8], arr2: [u8; 8], choice: bool) -> [u8; 8] {
    let arr = if choice { arr1 } else { arr2 };
    arr
}
";
    let unoptimized = compile(unoptimized).map_err(|e| e.prettify(unoptimized))?;
    let optimized = compile(optimized).map_err(|e| e.prettify(optimized))?;
    assert_eq!(
        unoptimized.circuit.gates.len(),
        optimized.circuit.gates.len()
    );
    Ok(())
}

#[test]
fn optimize_bit_shifts2() -> Result<(), String> {
    let unoptimized = "
pub fn main(arr1: [u32; 2], arr2: [u32; 2], choice: bool) -> [u8; 8] {
    let arr = if choice { arr1 } else { arr2 };
    [
        arr[0] as u8,
        (arr[0] >> 8u8) as u8,
        (arr[0] >> 16u8) as u8,
        (arr[0] >> 24u8) as u8,
        arr[1] as u8,
        (arr[1] >> 8u8) as u8,
        (arr[1] >> 16u8) as u8,
        (arr[1] >> 24u8) as u8,
    ]
}
";
    let optimized = "
pub fn main(arr1: [u8; 8], arr2: [u8; 8], choice: bool) -> [u8; 8] {
    let arr = if choice { arr1 } else { arr2 };
    arr
}
";
    let unoptimized = compile(unoptimized).map_err(|e| e.prettify(unoptimized))?;
    let optimized = compile(optimized).map_err(|e| e.prettify(optimized))?;
    assert_eq!(
        unoptimized.circuit.gates.len(),
        optimized.circuit.gates.len()
    );
    Ok(())
}
