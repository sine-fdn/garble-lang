use garble::{
    ast::Type, compile, eval::Evaluator, literal::Literal, token::UnsignedNumType, Error,
};

fn pretty_print<E: Into<Error>>(e: E, prg: &str) -> Error {
    let e: Error = e.into();
    let pretty = e.prettify(prg);
    println!("{}", pretty);
    e
}

#[test]
fn compile_xor() -> Result<(), Error> {
    for y in [true, false] {
        let prg = format!(
            "
pub fn main(x: bool) -> bool {{
    x ^ {}
}}
",
            y
        );
        let (typed_prg, main_fn, circuit) =
            compile(&prg, "main").map_err(|e| pretty_print(e, &prg))?;
        for x in [true, false] {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_bool(x);
            let output = eval.run().map_err(|e| pretty_print(e, &prg))?;
            assert_eq!(
                bool::try_from(output).map_err(|e| pretty_print(e, &prg))?,
                x ^ y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_add() -> Result<(), Error> {
    for y in 0..127 {
        let prg = format!(
            "
pub fn main(x: u8) -> u8 {{
    x + {}
}}
",
            y
        );
        let (typed_prg, main_fn, circuit) =
            compile(&prg, "main").map_err(|e| pretty_print(e, &prg))?;
        for x in 0..127 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            let output = eval.run().map_err(|e| pretty_print(e, &prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, &prg))?,
                x + y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_add_with_int_coercion() -> Result<(), Error> {
    for y in 240..280 {
        let prg = format!(
            "
pub fn main(x: u16) -> u16 {{
    x + {}
}}
",
            y
        );
        let (typed_prg, main_fn, circuit) =
            compile(&prg, "main").map_err(|e| pretty_print(e, &prg))?;
        for x in 240..280 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u16(x);
            let output = eval.run().map_err(|e| pretty_print(e, &prg))?;
            assert_eq!(
                u16::try_from(output).map_err(|e| pretty_print(e, &prg))?,
                x + y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_let_expr() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16) -> u16 {
    let y = x + 1;
    y + 1
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        257
    );
    Ok(())
}

#[test]
fn compile_static_fn_defs() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16) -> u16 {
    inc(x)
}

fn inc(x: u16) -> u16 {
    add(x, 1)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        256
    );
    Ok(())
}

#[test]
fn compile_if() -> Result<(), Error> {
    let prg = "
pub fn main(x: bool) -> u8 {
    if (true & false) ^ x {
        100u8
    } else {
        50u8
    }
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for b in [true, false] {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        let expected = if b { 100 } else { 50 };
        eval.set_bool(b);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_bit_ops_for_numbers() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16, y: u16, z: u16) -> u16 {
    x | (y & (z ^ 2))
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 10..20 {
        for y in 10..20 {
            for z in 10..20 {
                let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
                let expected = x | (y & (z ^ 2));
                eval.set_u16(x);
                eval.set_u16(y);
                eval.set_u16(z);
                let output = eval.run().map_err(|e| pretty_print(e, prg))?;
                assert_eq!(
                    u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
                    expected
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_greater_than_and_less_than() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16, y: u16) -> bool {
    (x > y) & (x < 10)
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 5..15 {
        for y in 5..15 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            let expected = (x > y) && (x < 10);
            eval.set_u16(x);
            eval.set_u16(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_equals_and_not_equals() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16, y: u16) -> bool {
    (x == y) & (x != 0)
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 0..2 {
        for y in 0..2 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            let expected = (x == y) && (x != 0);
            eval.set_u16(x);
            eval.set_u16(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_casts() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16, y: u8) -> u16 {
    (x as u8) as u16 + y as u16
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 200..300 {
        for y in 0..10 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            let expected = (x as u8) as u16 + y as u16;
            eval.set_u16(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_bool_casts() -> Result<(), Error> {
    let prg = "
pub fn main(x: bool, y: u8) -> u16 {
    x as u16 + y as u16
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in [true, false] {
        for y in 0..10 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            let expected = (x as u16) + (y as u16);
            eval.set_bool(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_bit_shifts() -> Result<(), Error> {
    let prg = "
pub fn main(mode: bool, x: u16, y: u8) -> u16 {
    if mode { x << y } else { x >> y }
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for mode in [true, false] {
        for x in 240..270 {
            for y in 0..20 {
                let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
                eval.set_bool(mode);
                eval.set_u16(x);
                eval.set_u8(y);
                let result = eval.run().map_err(|e| pretty_print(e, prg))?;
                let output = u16::try_from(result);
                if y >= 16 {
                    assert!(
                        output.is_err(),
                        "{x} {} {y}",
                        if mode { "<<" } else { ">>" }
                    )
                } else {
                    let expected = if mode { x << y } else { x >> y };
                    assert!(output.is_ok(), "{x} {} {y}", if mode { "<<" } else { ">>" });
                    assert_eq!(
                        output.unwrap(),
                        expected,
                        "{x} {} {y}",
                        if mode { "<<" } else { ">>" }
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
fn compile_bit_shifts_u16() -> Result<(), Error> {
    let prg = "
pub fn main(mode: bool, x: u16, y: u8) -> u16 {
    if mode { (x << y) } else { (x >> y) }
}
    ";

    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let eval = |x: u16, y: u8| -> Result<(u16, u16), Error> {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_bool(true);
        eval.set_u16(x);
        eval.set_u8(y);
        let result = eval.run().map_err(|e| pretty_print(e, prg))?;
        let result1 = u16::try_from(result)?;

        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_bool(false);
        eval.set_u16(x);
        eval.set_u8(y);
        let result = eval.run().map_err(|e| pretty_print(e, prg))?;
        let result2 = u16::try_from(result)?;

        Ok((result1, result2))
    };

    for x in [u16::MAX, u16::MAX >> 1, 1, 0] {
        for shifts in 0u8..(u16::BITS as u8 - 1) {
            assert_eq!(((x << shifts), (x >> shifts)), eval(x, shifts)?);
        }
    }

    Ok(())
}

#[test]
fn compile_signed_nums() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8) -> i8 {
    x
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(i8::try_from(output).map_err(|e| pretty_print(e, prg))?, x);
    }
    Ok(())
}

#[test]
fn compile_signed_add() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8, y: i8) -> i8 {
    x + y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -64..64 {
        for y in -64..63 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_i8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x + y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_bit_ops_for_signed_numbers() -> Result<(), Error> {
    let prg = "
pub fn main(x: i16, y: i16, z: i16) -> i16 {
    x | (y & (z ^ 2))
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for y in -10..10 {
            for z in -10..10 {
                let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
                let expected = x | (y & (z ^ 2));
                eval.set_i16(x);
                eval.set_i16(y);
                eval.set_i16(z);
                let output = eval.run().map_err(|e| pretty_print(e, prg))?;
                assert_eq!(
                    i16::try_from(output).map_err(|e| pretty_print(e, prg))?,
                    expected
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_greater_than_and_less_than() -> Result<(), Error> {
    let prg = "
pub fn main(x: i16, y: i16) -> bool {
    (x > y) & (y < x)
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for y in -10..10 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            let expected = (x > y) && (y < x);
            eval.set_i16(x);
            eval.set_i16(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_signed_bit_shifts() -> Result<(), Error> {
    let prg = "
pub fn main(mode: bool, x: i16, y: u8) -> i16 {
    if mode {
        x << y
    } else {
        x >> y
    }
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    let test_values = (-20..20)
        .into_iter()
        .chain(vec![i16::MAX, i16::MIN].into_iter());
    for x in test_values {
        for mode in [true, false] {
            for y in 0..20 {
                let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
                eval.set_bool(mode);
                eval.set_i16(x);
                eval.set_u8(y);
                let result = eval.run().map_err(|e| pretty_print(e, prg))?;
                let output = i16::try_from(result);
                if y >= 16 {
                    assert!(
                        output.is_err(),
                        "{x} {} {y}",
                        if mode { "<<" } else { ">>" }
                    )
                } else {
                    let expected = if mode { x << y } else { x >> y };
                    assert!(output.is_ok(), "{x} {} {y}", if mode { "<<" } else { ">>" });
                    assert_eq!(
                        output.unwrap(),
                        expected,
                        "{x} {} {y}",
                        if mode { "<<" } else { ">>" }
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
fn compile_add_with_signed_int_coercion() -> Result<(), Error> {
    let prg = "
pub fn main(x: i16) -> i16 {
    x + -10
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        let expected = x + -10;
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i16::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_unsigned_sub() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8, y: u8) -> u8 {
    x - y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in (0..=255).step_by(3) {
        for y in (0..=255).step_by(3) {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            eval.set_u8(y);
            let result = eval.run().map_err(|e| pretty_print(e, prg))?;
            let output = u8::try_from(result);
            if (x as i16 - y as i16) < 0 {
                assert!(output.is_err(), "{x} - {y}");
            } else {
                assert!(output.is_ok(), "{x} - {y}");
                assert_eq!(output.unwrap(), x - y, "{x} - {y}");
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_sub() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8, y: i8) -> i8 {
    x - y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in (-128..=127).step_by(3) {
        for y in (-128..=127).step_by(3) {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_i8(y);
            let result = eval.run().map_err(|e| pretty_print(e, prg))?;
            let output = i8::try_from(result);
            if (x as i16 - y as i16) < i8::MIN as i16 || (x as i16 - y as i16) > i8::MAX as i16 {
                assert!(output.is_err(), "{x} - {y}");
            } else {
                assert!(output.is_ok(), "{x} - {y}");
                assert_eq!(output.unwrap(), x - y, "{x} - {y}");
            }
        }
    }
    Ok(())
}

#[test]
fn compile_unary_negation() -> Result<(), Error> {
    let prg = "
pub fn main(x: i16) -> i16 {
    -x
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -127..127 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(i16::try_from(output).map_err(|e| pretty_print(e, prg))?, -x);
    }
    Ok(())
}

#[test]
fn compile_unary_not() -> Result<(), Error> {
    let prg = "
pub fn main(x: i16) -> i16 {
    !x
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -127..127 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(i16::try_from(output).map_err(|e| pretty_print(e, prg))?, !x);
    }

    let prg = "
pub fn main(x: bool) -> bool {
    !x
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for b in [true, false] {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_bool(b);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
            !b
        );
    }
    Ok(())
}

#[test]
fn compile_unsigned_mul() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8, y: u8) -> u8 {
    x * y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in (0..=255).step_by(3) {
        for y in (0..=255).step_by(3) {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            eval.set_u8(y);
            let result = eval.run().map_err(|e| pretty_print(e, prg))?;
            let output = u8::try_from(result);
            if (x as u16 * y as u16) > u8::MAX as u16 {
                assert!(output.is_err(), "{x} * {y}");
            } else {
                assert!(output.is_ok(), "{x} * {y}");
                assert_eq!(output.unwrap(), x * y, "{x} * {y}");
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_mul() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8, y: i8) -> i8 {
    x * y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in (-128..=127).step_by(3) {
        for y in (-128..=127).step_by(3) {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_i8(y);
            let result = eval.run().map_err(|e| pretty_print(e, prg))?;
            let output = i8::try_from(result);
            if (x as i16 * y as i16) < i8::MIN as i16 || (x as i16 * y as i16) > i8::MAX as i16 {
                assert!(output.is_err(), "{x} * {y}");
            } else {
                assert!(output.is_ok(), "{x} * {y}");
                assert_eq!(output.unwrap(), x * y, "{x} * {y}");
            }
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_div() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8, y: u8) -> u8 {
    x / y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 0..255 {
        for y in 1..10 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x / y
            );
        }
        for y in 250..255 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x / y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_mod() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8, y: u8) -> u8 {
    x % y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 0..255 {
        for y in 1..10 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x % y
            );
        }
        for y in 250..255 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x % y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_signed_div() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8, y: i8) -> i8 {
    x / y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        for y in -4..5 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            if y == -1 || y == 0 {
                continue;
            }
            eval.set_i8(x);
            eval.set_i8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x / y
            );
        }
        for y in 120..127 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_i8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x / y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_signed_mod() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8, y: i8) -> i8 {
    x % y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        for y in -4..5 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            if y == -1 || y == 0 {
                continue;
            }
            eval.set_i8(x);
            eval.set_i8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x % y
            );
        }
        for y in 120..127 {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_i8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x % y
            );
        }
    }
    Ok(())
}

#[test]
fn compile_array_repeat_literal_access() -> Result<(), Error> {
    let array_size = 256;
    let prg = &format!(
        "
pub fn main(x: i8, i: usize) -> i8 {{
    [x; {}][i]
}}
",
        array_size
    );
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for i in 0..array_size {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_usize(i);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(i8::try_from(output).map_err(|e| pretty_print(e, prg))?, x);
        }
    }
    Ok(())
}

#[test]
fn compile_array_assignment() -> Result<(), Error> {
    let array_size = 8;
    let prg = &format!(
        "
pub fn main(x: i8, i: usize, j: usize) -> i8 {{
    let arr = [x; {}];
    let arr = arr.update(i, x * 2);
    arr[j]
}}
",
        array_size
    );
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    let x = -5;
    for i in 0..array_size {
        for j in 0..array_size {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            let expected = if i == j { x * 2 } else { x };
            eval.set_i8(x);
            eval.set_usize(i);
            eval.set_usize(j);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_fold() -> Result<(), Error> {
    let array_size = 8;
    let prg = &format!(
        "
pub fn main(x: i8) -> i8 {{
    let arr = [x; {}];
    arr.fold(0, |acc: i8, x: i8| -> i8 {{
        acc + x
    }})
}}
",
        array_size
    );
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            array_size * x
        );
    }
    Ok(())
}

#[test]
fn compile_map() -> Result<(), Error> {
    let array_size = 8;
    let prg = &format!(
        "
pub fn main(x: i8, i: usize) -> i8 {{
    let arr = [x; {}];
    let arr = arr.map(|x: i8| -> i8 {{x * 2}});
    arr[i]
}}
",
        array_size
    );
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for i in 0..array_size {
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_i8(x);
            eval.set_usize(i);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x * 2
            );
        }
    }
    Ok(())
}

#[test]
fn compile_signed_casts() -> Result<(), Error> {
    // signed to unsigned:

    let prg = "pub fn main(x: i16) -> u8 { x as u8 }";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -200..200 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as u8
        );
    }

    let prg = "pub fn main(x: i8) -> u16 { x as u16 }";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as u16
        );
    }

    // unsigned to signed:

    let prg = "pub fn main(x: u16) -> i8 { x as i8 }";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 200..300 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_u16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i8
        );
    }

    let prg = "pub fn main(x: u8) -> i16 { x as i16 }";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 200..255 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_u8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i16::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i16
        );
    }

    // signed to signed:

    let prg = "pub fn main(x: i16) -> i8 { x as i8 }";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -200..200 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i8
        );
    }

    let prg = "pub fn main(x: i8) -> i16 { x as i16 }";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i16::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i16
        );
    }
    Ok(())
}

#[test]
fn compile_range() -> Result<(), Error> {
    let prg = "
pub fn main(_x: u8) -> i16 {
    let arr = 1..101;
    arr.fold(0, |acc: i16, x: usize| -> i16 {
        acc + (x as i16)
    })
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_u8(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        i16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        50 * 101
    );
    Ok(())
}

#[test]
fn compile_tuple() -> Result<(), Error> {
    for (t, i) in [("i32", 0), ("i16", 1), ("i8", 2), ("bool", 3), ("bool", 4)] {
        let prg = &format!(
            "
pub fn main(x: bool) -> {} {{
    let t = (-3, -2i16, -1i8, true, false);
    t.{}
}}
",
            t, i
        );
        let (typed_prg, main_fn, circuit) =
            compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_bool(false);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        match i {
            0 => assert_eq!(i32::try_from(output).map_err(|e| pretty_print(e, prg))?, -3),
            1 => assert_eq!(i16::try_from(output).map_err(|e| pretty_print(e, prg))?, -2),
            2 => assert_eq!(i8::try_from(output).map_err(|e| pretty_print(e, prg))?, -1),
            3 => assert_eq!(
                bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
                true
            ),
            4 => assert_eq!(
                bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
                false
            ),
            _ => unreachable!(),
        }
    }
    Ok(())
}

#[test]
fn compile_exhaustive_bool_pattern() -> Result<(), Error> {
    let prg = "
enum Foobar {
    Foo,
    Bar(bool, bool),
}

pub fn main(b: bool) -> i32 {
    let choice = if b {
        Foobar::Bar(true, false)
    } else {
        Foobar::Foo
    };
    match choice {
        Foobar::Bar(false, false) => 1,
        Foobar::Bar(false, true) => 2,
        Foobar::Bar(_, false) => 3,
        Foobar::Bar(true, true) => 4,
        Foobar::Foo => 5,
    }
}
";
    for b in [false, true] {
        let (typed_prg, main_fn, circuit) =
            compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_bool(b);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let result = i32::try_from(output).map_err(|e| pretty_print(e, prg))?;
        if b {
            assert_eq!(result, 3);
        } else {
            assert_eq!(result, 5);
        }
    }
    Ok(())
}

#[test]
fn compile_exhaustive_enum_pattern() -> Result<(), Error> {
    let prg = "
enum Foobar {
    Foo,
    Bar(u8)
}

pub fn main(b: bool) -> u8 {
    let choice = if b {
        Foobar::Bar(6)
    } else {
        Foobar::Foo
    };
    match choice {
        Foobar::Foo => 5 as u8,
        Foobar::Bar(x) => x
    }
}
";
    for b in [false, true] {
        let (typed_prg, main_fn, circuit) =
            compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_bool(b);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            (b as u8) + 5
        );
    }
    Ok(())
}

#[test]
fn compile_exhaustive_enum_pattern_with_literals() -> Result<(), Error> {
    let prg = "
enum Ops {
    Mul(u8, u8),
    Div(u8, u8),
}

pub fn main(choice: u8, x: u8, y: u8) -> u8 {
    let op = if choice == 0 {
        Ops::Mul(x, y)
    } else {
        Ops::Div(x, y)
    };

    match op {
        Ops::Div(x, 0) => 42 as u8,
        Ops::Div(x, y) => x / y,
        Ops::Mul(x, y) => x * y,
    }
}
";
    for choice in [0, 1] {
        for y in [0, 4] {
            let x = 10;
            let expected = if choice == 0 {
                x * y
            } else if y == 0 {
                42
            } else {
                x / y
            };
            let (typed_prg, main_fn, circuit) =
                compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
            let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
            eval.set_u8(choice);
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_exhaustive_range_pattern() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8) -> u8 {
    match x {
        0..10 => 1,
        10 => 2,
        11 => 2,
        13 => 2,
        12..100 => 2,
        100..256 => 3,
    } as u8
}
";
    for x in 0..255 {
        let (typed_prg, main_fn, circuit) =
            compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_u8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let expected = if x <= 9 {
            1
        } else if x <= 99 {
            2
        } else {
            3
        };
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_exhaustive_tuple_pattern() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8) -> u8 {
    let x = (false, x, -5);
    match x {
        (true, x, y) => 1u8,
        (false, 0, y) => 2u8,
        (false, x, y) => x,
    }
}
";
    for x in 0..10 {
        let (typed_prg, main_fn, circuit) =
            compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_u8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let expected = if x == 0 { 2 } else { x };
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_exhaustive_nested_pattern() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8) -> u8 {
    let x = (x, (x * 2, 1 as u8));
    match x {
        (0, _) => 1u8,
        (1..256, (x_twice, 1)) => x_twice,
        (1..256, (_, 1..256)) => 2u8,
        (1..256, (_, 0)) => 3u8,
    }
}
";
    for x in 0..10 {
        let (typed_prg, main_fn, circuit) =
            compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_u8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let expected = if x == 0 { 1 } else { x * 2 };
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_main_with_tuple_io() -> Result<(), Error> {
    let prg = "
pub fn main(values: (u8, u8)) -> (u8, u8) {
    (values.0 + 1, values.1 + 1)
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    let tuple_ty = Type::Tuple(vec![
        Type::Unsigned(UnsignedNumType::U8),
        Type::Unsigned(UnsignedNumType::U8),
    ]);
    let input = Literal::parse(&typed_prg, &tuple_ty, "(2u8, 3u8)")?;
    eval.set_literal(input)?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    let expected = Literal::parse(&typed_prg, &tuple_ty, "(3u8, 4u8)")?;
    assert_eq!(r, expected);
    Ok(())
}

#[test]
fn compile_main_with_enum_io() -> Result<(), Error> {
    let prg = "
enum Op {
    Zero,
    Div(u8, u8),
}

enum OpResult {
    DivByZero,
    Ok(u8),
}

pub fn main(op: Op) -> OpResult {
    match op {
        Op::Zero => OpResult::Ok(0),
        Op::Div(x, 0u8) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    let ty_in = Type::Enum("Op".to_string());
    let ty_out = Type::Enum("OpResult".to_string());
    let input = Literal::parse(&typed_prg, &ty_in, "Op::Div(10u8, 2u8)")?;
    eval.set_literal(input)?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    let expected = Literal::parse(&typed_prg, &ty_out, "OpResult::Ok(5)")?;
    assert_eq!(r, expected);
    Ok(())
}

#[test]
fn compile_array_literal_access() -> Result<(), Error> {
    let prg = "
pub fn main(i: usize) -> i32 {
    [-2, -1, 0, 1, 2][i]
}";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for i in 0..5 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_usize(i);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
            i as i32 - 2
        );
    }
    Ok(())
}

#[test]
fn compile_main_with_array_io() -> Result<(), Error> {
    let prg = "
pub fn main(nums: [u8; 5]) -> [u8; 5] {
    let sum = nums.fold(0, |acc: u16, n: u8| -> u16 {
        acc + (n as u16)
    });
    nums.map(|n: u8| -> u8 {
        sum as u8
    })
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;

    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    let array_ty = Type::Array(Box::new(Type::Unsigned(UnsignedNumType::U8)), 5);
    let input = Literal::parse(&typed_prg, &array_ty, "[1u8, 2u8, 3u8, 4u8, 5u8]")?;
    eval.set_literal(input)?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    let expected = Literal::parse(&typed_prg, &array_ty, "[15u8, 15u8, 15u8, 15u8, 15u8]")?;
    assert_eq!(r, expected);
    Ok(())
}

#[test]
fn compile_if_elseif_else() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8) -> i8 {
    if x < 0 {
        -1
    } else if x == 0 {
        0 as i8
    } else {
        1 as i8
    }
}
    ";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in [-2, -1, 0, 1, 2] {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        let expected = if x < 0 {
            -1
        } else if x == 0 {
            0
        } else {
            1
        };
        eval.set_i8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_lexically_scoped_block() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32) -> i32 {
    let y = x + 1;
    let z = {
        let y = x + 10;
        y
    };
    y
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    for x in 0..10 {
        let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let output = i32::try_from(output).map_err(|e| pretty_print(e, prg))?;
        assert_eq!(output, x + 1);
    }
    Ok(())
}

#[test]
fn compile_struct_type() -> Result<(), Error> {
    let prg = "
struct FooBar {
    foo: i32,
    bar: i32,
}

pub fn main(x: i32) -> i32 {
    let foobar = FooBar { foo: x, bar: 2 };
    foobar.bar
}
";
    let (typed_prg, main_fn, circuit) = compile(prg, "main").map_err(|e| pretty_print(e, prg))?;
    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_i32(5);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let output = i32::try_from(output).map_err(|e| pretty_print(e, prg))?;
    assert_eq!(output, 2);

    Ok(())
}
