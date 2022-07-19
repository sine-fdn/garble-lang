use garble_lang::{
    circuit::{EvalPanic, PanicReason},
    compile,
    eval::{EvalError, EvalOutput, Evaluator},
    Error,
};

#[test]
fn panic_on_unsigned_add_with_overflow() -> Result<(), String> {
    let prg = "
pub fn main(x: u8) -> u8 {
    x + 255u8
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_u8(1);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);
    Ok(())
}

#[test]
fn panic_on_signed_add_with_overflow() -> Result<(), String> {
    let prg = "
pub fn main(x: i8) -> i8 {
    x + -100i8
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i8(-100);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);
    Ok(())
}

#[test]
fn panic_on_sub_with_overflow() -> Result<(), String> {
    let prg = "
pub fn main(x: i8) -> i8 {
    x - 100i8
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i8(-100);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);
    Ok(())
}

#[test]
fn panic_on_div_by_zero() -> Result<(), String> {
    let prg = "
pub fn main(x: u8) -> u8 {
    x / 0u8
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_u8(1);
    let res = computation.run();
    expect_panic(res, PanicReason::DivByZero);
    Ok(())
}

#[test]
fn panic_in_branch_of_if_expr() -> Result<(), String> {
    let prg = "
pub fn main(b: bool) -> i32 {
    if b {
        1i32
    } else {
        1i32 / 0i32
    }
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_bool(true);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_bool(false);
    let res = computation.run();
    expect_panic(res, PanicReason::DivByZero);
    Ok(())
}

#[test]
fn panic_in_branch_of_match_expr() -> Result<(), String> {
    let prg = "
pub fn main(x: i32) -> i32 {
    match x {
        0i32 => 0i32,
        1i32 => 1i32 / 0i32,
        2i32 => 2i32,
        3i32 => (200u8 + 200u8) as i32,
        _ => 3i32,
    }
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i32(0);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i32(1);
    let res = computation.run();
    expect_panic(res, PanicReason::DivByZero);

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i32(2);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i32(3);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_i32(4);
    let res = computation.run();
    assert!(res.is_ok());

    Ok(())
}

#[test]
fn panic_on_out_of_bounds_access() -> Result<(), String> {
    let prg = "
pub fn main(i: usize) -> i32 {
    [1i32, 2i32, 3i32][i]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(0);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(1);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(2);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(3);
    let res = computation.run();
    expect_panic(res, PanicReason::OutOfBounds);

    Ok(())
}

#[test]
fn panic_on_out_of_bounds_update() -> Result<(), String> {
    let prg = "
pub fn main(i: usize) -> i32 {
    let mut updated = [1i32, 2i32, 3i32];
    updated[i] = 0i32;
    updated[0]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| e.prettify(prg))?;

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(0);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(1);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(2);
    let res = computation.run();
    assert!(res.is_ok());

    let mut computation = Evaluator::new(&typed_prg, &main_fn, &circuit);
    computation.set_usize(3);
    let res = computation.run();
    expect_panic(res, PanicReason::OutOfBounds);

    Ok(())
}

#[test]
fn panic_in_short_circuiting_and() -> Result<(), Error> {
    let prg = "
pub fn main(b: bool) -> bool {
    b & [true; 0][1]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let prg = "
pub fn main(b: bool) -> bool {
    b && [true; 0][1]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    let output = eval.run()?;
    let output = bool::try_from(output);
    assert!(output.is_ok());
    assert_eq!(output.unwrap(), false);

    let prg = "
pub fn main(b: bool) -> bool {
    [true; 0][1] && b
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let prg = "
pub fn main(b: bool) -> bool {
    (0i32 / 0i32 == 1i32) && [true; 0][1]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::DivByZero);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::DivByZero);

    Ok(())
}

#[test]
fn panic_in_short_circuiting_or() -> Result<(), Error> {
    let prg = "
pub fn main(b: bool) -> bool {
    b | [true; 0][1]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let prg = "
pub fn main(b: bool) -> bool {
    b || [true; 0][1]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    let output = eval.run()?;
    let output = bool::try_from(output);
    assert!(output.is_ok());
    assert_eq!(output.unwrap(), true);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let prg = "
pub fn main(b: bool) -> bool {
    [true; 0][1] || b
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::OutOfBounds);

    let prg = "
pub fn main(b: bool) -> bool {
    (0i32 / 0i32 == 1i32) || [true; 0][1]
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(true);
    expect_panic(eval.run(), PanicReason::DivByZero);

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_bool(false);
    expect_panic(eval.run(), PanicReason::DivByZero);

    Ok(())
}

fn expect_panic(eval_result: Result<EvalOutput, EvalError>, expected: PanicReason) {
    assert!(eval_result.is_ok());
    let eval_output = Vec::<bool>::try_from(eval_result.unwrap());
    assert!(eval_output.is_err());
    match eval_output.unwrap_err() {
        EvalError::Panic(EvalPanic { reason, .. }) => assert_eq!(expected, reason),
        e => panic!("Expected a panic, but found {:?}", e),
    }
}

fn pretty_print<E: Into<Error>>(e: E, prg: &str) -> Error {
    let e: Error = e.into();
    let pretty = e.prettify(prg);
    println!("{}", pretty);
    e
}
