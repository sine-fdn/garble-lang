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
fn optimize_same_expr2() -> Result<(), String> {
    let unoptimized = "
pub fn main(x: i32) -> i32 {
    (x * x) + (x * x)
}
";
    let optimized = "
pub fn main(x: i32) -> i32 {
    let y = x * x;
    y + y
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
fn optimize_same_expr3() -> Result<(), String> {
    let unoptimized = "
pub fn main(input1: i8, input2: i8) -> bool {
	let _unused = add(input1, input2);
	square(input1) < input2 || square(input1) > input2
}

fn square(num: i8) -> i8 {
	num * num
}

fn add(a: i8, b: i8) -> i8 {
    a + b
}
";
    let optimized = "
pub fn main(input1: i8, input2: i8) -> bool {
	let _unused = add(input1, input2);
	let squared = square(input1);
	squared < input2 || squared > input2
}

fn square(num: i8) -> i8 {
	num * num
}

fn add(a: i8, b: i8) -> i8 {
    a + b
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

#[test]
fn optimize_mapped_arrays() -> Result<(), String> {
    let prg = "
pub fn main(arr1: [(u16, u16, u32); 8]) -> [((u16, u16), u32); 8] {
    let mut arr2 = [((0u16, 0u16), 0u32); 8];
    let mut i = 0usize;
    for elem in arr1 {
        let (a, b, c) = elem;
        arr2[i] = ((a, b), c);
        i = i + 1usize;
    }
    arr2
}";
    let compiled = compile(prg).map_err(|e| e.prettify(prg))?;
    assert_eq!(compiled.circuit.and_gates(), 0);
    assert_eq!(compiled.circuit.gates.len(), 2);
    Ok(())
}

// Run the following test using `cargo test plot --features=plot --release -- --nocapture`

#[test]
#[cfg(feature = "plot")]
fn plot_for_each_join_loop_complexity() -> Result<(), String> {
    use garble_lang::{compile_with_constants, literal::Literal, token::UnsignedNumType};
    use plotters::prelude::*;
    use std::collections::HashMap;

    let max_rows = 1000;

    let prg_nested_loop = "
const ROWS_0: usize = PARTY_0::ROWS_0;
const ROWS_1: usize = PARTY_1::ROWS_1;
pub fn main(rows0: [([u8; 8], u32); ROWS_0], rows1: [([u8; 8], u32); ROWS_1]) -> u32 {
    let mut result = 0u32;
    for row0 in rows0 {
        for row1 in rows1 {
            let (id0, a) = row0;
            let (id1, b) = row1;
            if id0 == id1 {
                result = result + a + b;
            }
        }
    }
    result
}
";
    let prg_join = "
const ROWS_0: usize = PARTY_0::ROWS_0;
const ROWS_1: usize = PARTY_1::ROWS_1;
pub fn main(rows0: [([u8; 8], u32); ROWS_0], rows1: [([u8; 8], u32); ROWS_1]) -> u32 {
    let mut result = 0u32;
    for joined in join(rows0, rows1) {
        let ((_, a), (_, b)) = joined;
        result = result + a + b;
    }
    result
}
";
    let mut all_gates_joined = vec![];
    let mut and_gates_joined = vec![];
    let mut all_gates_nested = vec![];
    let mut and_gates_nested = vec![];
    let mut max_gates = 0.0;
    for n in (0..=max_rows).step_by(20) {
        let consts = HashMap::from_iter(vec![
            (
                "PARTY_0".to_string(),
                HashMap::from_iter(vec![(
                    "ROWS_0".to_string(),
                    Literal::NumUnsigned(n, UnsignedNumType::Usize),
                )]),
            ),
            (
                "PARTY_1".to_string(),
                HashMap::from_iter(vec![(
                    "ROWS_1".to_string(),
                    Literal::NumUnsigned(n, UnsignedNumType::Usize),
                )]),
            ),
        ]);
        let compiled =
            compile_with_constants(prg_join, consts.clone()).map_err(|e| format!("{e:?}"))?;
        println!("{n} (joined): {}", compiled.circuit.report_gates());
        all_gates_joined.push((n as f32, compiled.circuit.gates.len() as f32 / 1_000_000.0));
        and_gates_joined.push((n as f32, compiled.circuit.and_gates() as f32 / 1_000_000.0));

        if n <= 250 {
            let compiled =
                compile_with_constants(prg_nested_loop, consts).map_err(|e| format!("{e:?}"))?;
            println!("{n} (nested): {}", compiled.circuit.report_gates());
            all_gates_nested.push((n as f32, compiled.circuit.gates.len() as f32 / 1_000_000.0));
            and_gates_nested.push((n as f32, compiled.circuit.and_gates() as f32 / 1_000_000.0));
            let all_gates = compiled.circuit.gates.len() as f32 / 1_000_000.0;
            if all_gates > max_gates {
                max_gates = all_gates;
            }
        }
    }

    let root = SVGBackend::new("plot_for_each_join_loop.svg", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let mut chart = ChartBuilder::on(&root)
        .caption(
            "Joined Rows vs. Circuit Size",
            ("sans-serif", 32).into_font(),
        )
        .margin(50)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(0f32..(max_rows as f32), 0f32..max_gates)
        .unwrap();

    chart.configure_mesh().draw().unwrap();

    chart
        .draw_series(LineSeries::new(all_gates_nested, &GREEN))
        .unwrap()
        .label("Million Gates (Nested)")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &GREEN));

    chart
        .draw_series(LineSeries::new(and_gates_nested, &BLUE))
        .unwrap()
        .label("Million AND Gates (Nested)")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &BLUE));

    chart
        .draw_series(LineSeries::new(all_gates_joined, &RED))
        .unwrap()
        .label("Million Gates (Join)")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &RED));

    chart
        .draw_series(LineSeries::new(and_gates_joined, &MAGENTA))
        .unwrap()
        .label("Million AND Gates (Join)")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &MAGENTA));

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()
        .unwrap();

    root.present().unwrap();
    Ok(())
}
