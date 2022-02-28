use garble::compile;

#[test]
fn optimize_or() -> Result<(), String> {
    let unoptimized = "
fn main(x: bool) -> bool {
    x | true
}
";
    let optimized = "
fn main(_x: bool) -> bool {
    true
}
";
    let unoptimized = compile(&unoptimized).map_err(|e| e.prettify(&unoptimized))?;
    let optimized = compile(&optimized).map_err(|e| e.prettify(&optimized))?;

    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_const_add() -> Result<(), String> {
    let unoptimized = "
fn main(_x: i32) -> i32 {
    1 + 2 + 3 + 4
}
";
    let optimized = "
fn main(_x: i32) -> i32 {
    10
}
";
    let unoptimized = compile(&unoptimized).map_err(|e| e.prettify(&unoptimized))?;
    let optimized = compile(&optimized).map_err(|e| e.prettify(&optimized))?;

    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_same_expr() -> Result<(), String> {
    let unoptimized = "
fn main(b: bool, x: i32) -> i32 {
    if b { x * x } else { x * x }
}
";
    let optimized = "
fn main(b: bool, x: i32) -> i32 {
    let y = x * x;
    if b { y } else { y }
}
";
    let unoptimized = compile(&unoptimized).map_err(|e| e.prettify(&unoptimized))?;
    let optimized = compile(&optimized).map_err(|e| e.prettify(&optimized))?;
    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_not_equivalence() -> Result<(), String> {
    let unoptimized = "
fn main(b: bool) -> bool {
    !(!b)
}
";
    let optimized = "
fn main(b: bool) -> bool {
    b
}
";
    let unoptimized = compile(&unoptimized).map_err(|e| e.prettify(&unoptimized))?;
    let optimized = compile(&optimized).map_err(|e| e.prettify(&optimized))?;
    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_or_and_equivalence1() -> Result<(), String> {
    let unoptimized = "
fn main(x: bool, y: bool) -> bool {
    x | (!x & y)
}
";
    let optimized = "
fn main(x: bool, y: bool) -> bool {
    x | y
}
";
    let unoptimized = compile(&unoptimized).map_err(|e| e.prettify(&unoptimized))?;
    let optimized = compile(&optimized).map_err(|e| e.prettify(&optimized))?;
    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}

#[test]
fn optimize_or_and_equivalence2() -> Result<(), String> {
    let unoptimized = "
fn main(x: bool, y: bool) -> bool {
    x & (!x | y)
}
";
    let optimized = "
fn main(x: bool, y: bool) -> bool {
    x & y
}
";
    let unoptimized = compile(&unoptimized).map_err(|e| e.prettify(&unoptimized))?;
    let optimized = compile(&optimized).map_err(|e| e.prettify(&optimized))?;
    assert_eq!(unoptimized.gates.len(), optimized.gates.len());
    Ok(())
}
