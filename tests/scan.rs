use garble_lang::scan::{ScanError, scan};

#[test]
fn scan_exhaustive_enum_pattern_with_literals() -> Result<(), Vec<ScanError>> {
    let prg = "
enum Ops {
    Mul(u8, u8),
    Div(u8, u8),
}

fn main(choice: A::u8, x: A::u8, y: A::u8) -> u8 {
    let op = if choice == 0 {
        Ops::Mul(x, y)
    } else {
        Ops::Div(x, y)
    };

    match op {
        Div(x, 0) => 42,
        Div(x, y) => x / y,
        Mul(x, y) => x * y,
    }
}
";
    scan(prg)?;
    Ok(())
}
