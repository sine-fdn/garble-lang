use garble::{
    circuit::{EvalPanic, PanicReason},
    compile,
    eval::{EvalError, Evaluator},
};

#[test]
fn panic_on_unsigned_add_with_overflow() -> Result<(), String> {
    let prg = "
fn main(x: u8) -> u8 {
    x + 255
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);
    computation.set_u8(1);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);
    Ok(())
}

#[test]
fn panic_on_signed_add_with_overflow() -> Result<(), String> {
    let prg = "
fn main(x: i8) -> i8 {
    x + -100
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);
    computation.set_i8(-100);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);
    Ok(())
}

#[test]
fn panic_on_sub_with_overflow() -> Result<(), String> {
    let prg = "
fn main(x: i8) -> i8 {
    x - 100
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);
    computation.set_i8(-100);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);
    Ok(())
}

#[test]
fn panic_on_div_by_zero() -> Result<(), String> {
    let prg = "
fn main(x: u8) -> u8 {
    x / 0
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);
    computation.set_u8(1);
    let res = computation.run();
    expect_panic(res, PanicReason::DivByZero);
    Ok(())
}

#[test]
fn panic_in_branch_of_if_expr() -> Result<(), String> {
    let prg = "
fn main(b: bool) -> i32 {
    if b {
        1
    } else {
        1 / 0
    }
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);
    computation.set_bool(true);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_bool(false);
    let res = computation.run();
    expect_panic(res, PanicReason::DivByZero);
    Ok(())
}

#[test]
fn panic_in_branch_of_match_expr() -> Result<(), String> {
    let prg = "
fn main(x: i32) -> i32 {
    match x {
        0 => 0,
        1 => 1 / 0,
        2 => 2,
        3 => (200u8 + 200u8) as i32,
        _ => 3,
    }
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);

    computation.set_i32(0);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_i32(1);
    let res = computation.run();
    expect_panic(res, PanicReason::DivByZero);

    computation.set_i32(2);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_i32(3);
    let res = computation.run();
    expect_panic(res, PanicReason::Overflow);

    computation.set_i32(4);
    let res = computation.run();
    assert!(res.is_ok());

    Ok(())
}

#[test]
fn panic_on_out_of_bounds_access() -> Result<(), String> {
    let prg = "
fn main(i: usize) -> i32 {
    [1, 2, 3][i]
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);

    computation.set_usize(0);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_usize(1);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_usize(2);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_usize(3);
    let res = computation.run();
    expect_panic(res, PanicReason::OutOfBounds);

    Ok(())
}

#[test]
fn panic_on_out_of_bounds_update() -> Result<(), String> {
    let prg = "
fn main(i: usize) -> i32 {
    let updated = [1, 2, 3].update(i, 0);
    updated[0]
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut computation = Evaluator::from(circuit);

    computation.set_usize(0);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_usize(1);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_usize(2);
    let res = computation.run();
    assert!(res.is_ok());

    computation.set_usize(3);
    let res = computation.run();
    expect_panic(res, PanicReason::OutOfBounds);

    Ok(())
}

fn expect_panic(computation: Result<(), EvalError>, expected: PanicReason) {
    assert!(computation.is_err());
    match computation.unwrap_err() {
        EvalError::Panic(EvalPanic { reason, .. }) => assert_eq!(expected, reason),
        e => panic!("Expected a panic, but found {:?}", e),
    }
}
