use garble::compile;

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
    let (_, _, unoptimized) = compile(unoptimized, "main").map_err(|e| e.prettify(unoptimized))?;
    let (_, _, optimized) = compile(optimized, "main").map_err(|e| e.prettify(optimized))?;

    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_const_add() -> Result<(), String> {
    let unoptimized = "
pub fn main(_x: i32) -> i32 {
    1 + 2 + 3 + 4
}
";
    let optimized = "
pub fn main(_x: i32) -> i32 {
    10
}
";
    let (_, _, unoptimized) = compile(unoptimized, "main").map_err(|e| e.prettify(unoptimized))?;
    let (_, _, optimized) = compile(optimized, "main").map_err(|e| e.prettify(optimized))?;

    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_same_expr() -> Result<(), String> {
    let unoptimized = "
pub fn main(b: bool, x: i32) -> i32 {
    if b { x % x } else { x % x }
}
";
    let optimized = "
pub fn main(b: bool, x: i32) -> i32 {
    let y = x % x;
    if b { y } else { y }
}
";
    let (_, _, unoptimized) = compile(unoptimized, "main").map_err(|e| e.prettify(unoptimized))?;
    let (_, _, optimized) = compile(optimized, "main").map_err(|e| e.prettify(optimized))?;
    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
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
    let (_, _, unoptimized) = compile(unoptimized, "main").map_err(|e| e.prettify(unoptimized))?;
    let (_, _, optimized) = compile(optimized, "main").map_err(|e| e.prettify(optimized))?;
    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}
