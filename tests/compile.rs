use std::collections::HashMap;

use garble_lang::{
    compile, compile_with_constants, literal::Literal, token::UnsignedNumType, Error,
};

fn pretty_print<E: Into<Error>>(e: E, prg: &str) -> Error {
    let e: Error = e.into();
    let pretty = e.prettify(prg);
    println!("{pretty}");
    e
}

#[test]
fn compile_xor() -> Result<(), Error> {
    for y in [true, false] {
        let prg = format!(
            "
pub fn main(x: bool) -> bool {{
    x ^ {y}
}}
"
        );
        let compiled = compile(&prg).map_err(|e| pretty_print(e, &prg))?;
        for x in [true, false] {
            let mut eval = compiled.evaluator();
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
    x + {y}u8
}}
"
        );
        let compiled = compile(&prg).map_err(|e| pretty_print(e, &prg))?;
        for x in 0..127 {
            let mut eval = compiled.evaluator();
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
    x + {y}u16
}}
"
        );
        let compiled = compile(&prg).map_err(|e| pretty_print(e, &prg))?;
        for x in 240..280 {
            let mut eval = compiled.evaluator();
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
    let y = x + 1u16;
    y + 1u16
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
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
    add(x, 1u16)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for b in [true, false] {
        let mut eval = compiled.evaluator();
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
    x | (y & (z ^ 2u16))
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 10..20 {
        for y in 10..20 {
            for z in 10..20 {
                let mut eval = compiled.evaluator();
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
    (x > y) & (x < 10u16)
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 5..15 {
        for y in 5..15 {
            let mut eval = compiled.evaluator();
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
    (x == y) & (x != 0u16)
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..2 {
        for y in 0..2 {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 200..300 {
        for y in 0..10 {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in [true, false] {
        for y in 0..10 {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for mode in [true, false] {
        for x in 240..270 {
            for y in 0..20 {
                let mut eval = compiled.evaluator();
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

    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let eval = |x: u16, y: u8| -> Result<(u16, u16), Error> {
        let mut eval = compiled.evaluator();
        eval.set_bool(true);
        eval.set_u16(x);
        eval.set_u8(y);
        let result = eval.run().map_err(|e| pretty_print(e, prg))?;
        let result1 = u16::try_from(result)?;

        let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -64..64 {
        for y in -64..63 {
            let mut eval = compiled.evaluator();
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
    x | (y & (z ^ 2i16))
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for y in -10..10 {
            for z in -10..10 {
                let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for y in -10..10 {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let test_values = (-20..20).chain(vec![i16::MAX, i16::MIN].into_iter());
    for x in test_values {
        for mode in [true, false] {
            for y in 0..20 {
                let mut eval = compiled.evaluator();
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
    x + -10i16
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in (0..=255).step_by(3) {
        for y in (0..=255).step_by(3) {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in (-128..=127).step_by(3) {
        for y in (-128..=127).step_by(3) {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -127..127 {
        let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -127..127 {
        let mut eval = compiled.evaluator();
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(i16::try_from(output).map_err(|e| pretty_print(e, prg))?, !x);
    }

    let prg = "
pub fn main(x: bool) -> bool {
    !x
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for b in [true, false] {
        let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in (0..=255).step_by(3) {
        for y in (0..=255).step_by(3) {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in (-128..=127).step_by(3) {
        for y in (-128..=127).step_by(3) {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..255 {
        for y in 1..10 {
            let mut eval = compiled.evaluator();
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x / y
            );
        }
        for y in 250..255 {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..255 {
        for y in 1..10 {
            let mut eval = compiled.evaluator();
            eval.set_u8(x);
            eval.set_u8(y);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            assert_eq!(
                u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
                x % y
            );
        }
        for y in 250..255 {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        for y in -4..5 {
            let mut eval = compiled.evaluator();
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
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        for y in -4..5 {
            let mut eval = compiled.evaluator();
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
            let mut eval = compiled.evaluator();
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
    [x; {array_size}][i]
}}
"
    );
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for i in 0..array_size {
            let mut eval = compiled.evaluator();
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
    let mut arr = [x; {array_size}];
    arr[i] = x * 2i8;
    arr[j]
}}
"
    );
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let x = -5;
    for i in 0..array_size {
        for j in 0..array_size {
            let mut eval = compiled.evaluator();
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
    let mut arr = [x; {array_size}];
    let mut acc = 0i8;
    for elem in arr {{
        acc = acc + elem;
    }}
    acc
}}
"
    );
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        let mut eval = compiled.evaluator();
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
    let mut arr = [x; {array_size}];
    for j in 0usize..{array_size}usize {{
        arr[j] = arr[j] * 2i8;
    }}
    arr[i]
}}
"
    );
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -10..10 {
        for i in 0..array_size {
            let mut eval = compiled.evaluator();
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
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -200..200 {
        let mut eval = compiled.evaluator();
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            u8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as u8
        );
    }

    let prg = "pub fn main(x: i8) -> u16 { x as u16 }";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        let mut eval = compiled.evaluator();
        eval.set_i8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as u16
        );
    }

    // unsigned to signed:

    let prg = "pub fn main(x: u16) -> i8 { x as i8 }";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 200..300 {
        let mut eval = compiled.evaluator();
        eval.set_u16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i8
        );
    }

    let prg = "pub fn main(x: u8) -> i16 { x as i16 }";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 200..255 {
        let mut eval = compiled.evaluator();
        eval.set_u8(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i16::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i16
        );
    }

    // signed to signed:

    let prg = "pub fn main(x: i16) -> i8 { x as i8 }";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -200..200 {
        let mut eval = compiled.evaluator();
        eval.set_i16(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i8::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x as i8
        );
    }

    let prg = "pub fn main(x: i8) -> i16 { x as i16 }";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -128..127 {
        let mut eval = compiled.evaluator();
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
    let arr = 1u8..101u8;
    let mut acc = 0i16;
    for i in arr {{
        acc = acc + i as i16;
    }}
    acc
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
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
pub fn main(x: bool) -> {t} {{
    let t = (-3i32, -2i16, -1i8, true, false);
    t.{i}
}}
"
        );
        let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
        let mut eval = compiled.evaluator();
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
        Foobar::Bar(false, false) => 1i32,
        Foobar::Bar(false, true) => 2i32,
        Foobar::Bar(_, false) => 3i32,
        Foobar::Bar(true, true) => 4i32,
        Foobar::Foo => 5i32,
    }
}
";
    for b in [false, true] {
        let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
        let mut eval = compiled.evaluator();
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
        Foobar::Bar(6u8)
    } else {
        Foobar::Foo
    };
    match choice {
        Foobar::Foo => 5u8,
        Foobar::Bar(x) => x
    }
}
";
    for b in [false, true] {
        let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
        let mut eval = compiled.evaluator();
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
    let op = if choice == 0u8 {
        Ops::Mul(x, y)
    } else {
        Ops::Div(x, y)
    };

    match op {
        Ops::Div(x, 0u8) => 42u8,
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
            let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
            let mut eval = compiled.evaluator();
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
        0u8..10u8 => 1u8,
        10u8 => 2u8,
        11u8 => 2u8,
        13u8 => 2u8,
        12u8..100u8 => 2u8,
        100u8..=255u8 => 3u8,
    }
}
";
    for x in 0..255 {
        let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
        let mut eval = compiled.evaluator();
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
    let x = (false, x, -5i32);
    match x {
        (true, x, y) => 1u8,
        (false, 0u8, y) => 2u8,
        (false, x, y) => x,
    }
}
";
    for x in 0..10 {
        let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
        let mut eval = compiled.evaluator();
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
    let x = (x, (x * 2u8, 1u8));
    match x {
        (0u8, _) => 1u8,
        (1u8..=255u8, (x_twice, 1u8)) => x_twice,
        (1u8..=255u8, (_, 1u8..=255u8)) => 2u8,
        (1u8..=255u8, (_, 0u8)) => 3u8,
    }
}
";
    for x in 0..10 {
        let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
        let mut eval = compiled.evaluator();
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
    (values.0 + 1u8, values.1 + 1u8)
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "(2u8, 3u8)")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(format!("{r}"), "(3u8, 4u8)");
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
        Op::Zero => OpResult::Ok(0u8),
        Op::Div(x, 0u8) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "Op::Div(10u8, 2u8)")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "OpResult::Ok(5u8)");
    Ok(())
}

#[test]
fn compile_array_literal_access() -> Result<(), Error> {
    let prg = "
pub fn main(i: usize) -> i32 {
    [-2i32, -1i32, 0i32, 1i32, 2i32][i]
}";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for i in 0..5 {
        let mut eval = compiled.evaluator();
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
    let mut sum = 0u16;
    for n in nums {
        sum = sum + n as u16;
    }
    let mut nums = [0u8; 5];
    for i in 0usize..5usize {
        nums[i] = sum as u8;
    }
    nums
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "[1u8, 2u8, 3u8, 4u8, 5u8]")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "[15u8, 15u8, 15u8, 15u8, 15u8]");
    Ok(())
}

#[test]
fn compile_if_elseif_else() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8) -> i8 {
    if x < 0i8 {
        -1i8
    } else if x == 0i8 {
        0i8
    } else {
        1i8
    }
}
    ";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in [-2, -1, 0, 1, 2] {
        let mut eval = compiled.evaluator();
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
fn compile_if_elseif_else_assignment() -> Result<(), Error> {
    let prg = "
    pub fn main(income: u32) -> bool {
      let mut points = 0u16;

      if income >= 10000u32 {
        points = points + 200u16
      } else if income >= 2000u32 {
        points = points + 50u16
      } else {
        points = points + 0u16
      }

      if points > 150u16 {
        true
      } else {
        false
      }
    }

    ";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in [0, 10000] {
        let mut eval = compiled.evaluator();
        let expected = x != 0;
        eval.set_u32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_lexically_scoped_block() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32) -> i32 {
    let y = x + 1i32;
    let z = {
        let y = x + 10i32;
        y
    };
    y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..10 {
        let mut eval = compiled.evaluator();
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
    let foobar = FooBar { foo: x, bar: 2i32 };
    foobar.bar
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_i32(5);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let output = i32::try_from(output).map_err(|e| pretty_print(e, prg))?;
    assert_eq!(output, 2);

    Ok(())
}

#[test]
fn compile_struct_pattern() -> Result<(), Error> {
    let prg = "
struct FooBarBaz {
    foo: i32,
    bar: u8,
    baz: bool,
}

pub fn main(x: FooBarBaz) -> FooBarBaz {
    match x {
        FooBarBaz { foo: 1i32, bar: 0u8, baz: false } => FooBarBaz { baz: true, foo: 1i32, bar: 1u8 },
        FooBarBaz { foo: 1i32, baz, bar: 0u8 } => FooBarBaz { foo: 1i32, bar: 1u8, baz },
        FooBarBaz { bar, baz: false, foo } => FooBarBaz { foo, bar, baz: true },
        FooBarBaz { foo, bar, baz } => FooBarBaz { foo, bar: 1u8, baz },
        FooBarBaz { foo, .. } => FooBarBaz { foo, bar: 1u8, baz: true },
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "FooBarBaz { foo: 1i32, bar: 0u8, baz: true }")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "FooBarBaz {bar: 1u8, baz: true, foo: 1i32}");
    Ok(())
}

#[test]
fn compile_comments() -> Result<(), Error> {
    let prg = "
/*
fn unused_fn(x: ...) -> ... {
    /* nested block comment */
    // normal comment within block comment
}
 */
pub fn main(x: u16) -> u16 {
    // comment including '/*'
    x + /* ... */ 1u16
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(1);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(u16::try_from(output).map_err(|e| pretty_print(e, prg))?, 2);
    Ok(())
}

#[test]
fn compile_let_destructuring() -> Result<(), Error> {
    let prg = "
struct FooBar {
    foo: i32,
    bar: (i32, i32),
}

pub fn main(x: (i32, i32)) -> i32 {
    let (a, b) = x;

    let bar = (0i32, 0i32);
    let foobar = FooBar { foo: 0i32, bar };
    let FooBar { bar, .. } = foobar;
    let (y, z) = bar;
    a + y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_literal(compiled.parse_arg(0, "(1i32, 2i32)")?.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(i32::try_from(output).map_err(|e| pretty_print(e, prg))?, 1);
    Ok(())
}

#[test]
fn compile_struct_sugar() -> Result<(), Error> {
    let prg = "
struct FooBar {
    foo: i32,
    bar: i32,
}

pub fn main(x: (i32, i32)) -> i32 {
    let (foo, bar) = x;
    let foobar = FooBar { foo, bar };
    match foobar {
        FooBar { foo: 0i32, .. } => 1i32,
        FooBar { foo, .. } => foo,
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_literal(compiled.parse_arg(0, "(2i32, 3i32)")?.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(i32::try_from(output).map_err(|e| pretty_print(e, prg))?, 2);
    Ok(())
}

#[test]
fn compile_struct_shorthand() -> Result<(), Error> {
    let prg = "
struct FooBar {
    foo: i32,
    bar: (i32, i32),
    baz: (i32, i32, i32),
}

pub fn main(x: i32) -> i32 {
    let foobar = FooBar {
        foo: 1i32,
        bar: (2i32, 3i32),
        baz: (4i32, 5i32, 6i32),
    };
    match x {
        0i32 => {
            let FooBar { foo, .. } = foobar;
            foo
        },
        1i32 => {
            let FooBar { bar, .. } = foobar;
            let (x, y) = bar;
            y
        },
        _ => {
            let FooBar { baz, .. } = foobar;
            let (x, y, z) = baz;
            z
        }
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in [0, 1, 2] {
        let expected = match x {
            0 => 1,
            1 => 3,
            _ => 6,
        };
        let mut eval = compiled.evaluator();
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_mutable_bindings() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32) -> i32 {
    let mut y = 0i32;
    y = x;
    y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in -20..20 {
        let mut eval = compiled.evaluator();
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(i32::try_from(output).map_err(|e| pretty_print(e, prg))?, x);
    }
    Ok(())
}

#[test]
fn compile_mutable_bindings_inside_if() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32, b: bool) -> i32 {
    let mut y = 0i32;
    if b {
        y = x;
    }
    y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for b in [true, false] {
        for x in -20..20 {
            let mut eval = compiled.evaluator();
            eval.set_i32(x);
            eval.set_bool(b);
            let output = eval.run().map_err(|e| pretty_print(e, prg))?;
            let expected = if b { x } else { 0 };
            assert_eq!(
                i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_mutable_bindings_inside_match() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32) -> i32 {
    let mut y = 0i32;
    match x {
        0i32 => {},
        1i32..10i32 => {
            y = 1i32;
        },
        10i32..100i32 => {
            y = 2i32;
        },
        _ => {
            y = 3i32;
        }
    }
    y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..110 {
        let mut eval = compiled.evaluator();
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let expected = match x {
            0 => 0,
            1..=9 => 1,
            10..=99 => 2,
            _ => 3,
        };
        assert_eq!(
            i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_for_loop() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32) -> i32 {
    let mut y = x;
    for i in 0u8..10u8 {
        y = y + i as i32;
    }
    y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..110 {
        let mut eval = compiled.evaluator();
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
            x + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9,
        );
    }
    Ok(())
}

#[test]
fn compile_for_loop_over_array() -> Result<(), Error> {
    let prg = "
pub fn main(_x: i32) -> i32 {
    let mut sum = 0i32;
    for i in [2i32, 4i32, 6i32, 8i32] {
        sum = sum + i
    }
    sum
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..110 {
        let mut eval = compiled.evaluator();
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
            2 + 4 + 6 + 8,
        );
    }
    Ok(())
}

#[test]
fn compile_array_assign_inside_for_loop() -> Result<(), Error> {
    let prg = "
pub fn main(_x: i32) -> [i32; 5] {
    let mut array = [0i32; 5];
    for i in 0u8..5u8 {
        array[i as usize] = i as i32 * 2i32;
    }
    array
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_i32(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "[0i32, 2i32, 4i32, 6i32, 8i32]");
    Ok(())
}

#[test]
fn compile_arrays_copied_by_value() -> Result<(), Error> {
    let prg = "
pub fn main(replacement: i32) -> [i32; 4] {
    let mut array1 = [10i32, 20i32, 30i32, 40i32];
    let second_val = array1[1]; // will be `20i32`
    let mut array2 = array1;
    array2[1] = replacement;
    let second_val1 = array1[1]; // will still be `20i32`
    let second_val2 = array2[1]; // will be equal to the value of `replacement`
    array2
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for x in 0..110 {
        let mut eval = compiled.evaluator();
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(r.to_string(), format!("[10i32, {x}i32, 30i32, 40i32]"));
    }
    Ok(())
}

#[test]
fn compile_operator_examples() -> Result<(), Error> {
    let prg = "
pub fn main(_a: i32, _b: i32) -> () {
    let add = 0i32 + 1i32;
    let sub = 1i32 - 1i32;
    let mul = 2i32 * 1i32;
    let div = 2i32 / 1i32;
    let rem = 5i32 % 2i32;

    let bit_xor = 4u32 ^ 6u32;
    let bit_and = 4u32 & 6u32;
    let bit_or = 4u32 | 6u32;
    let bit_shiftl = 4u32 << 1u8;
    let bit_shiftr = 4u32 >> 1u8;

    let and = true & false;
    let or = true | false;

    let eq = true == false;
    let neq = true != false;

    let gt = 5i32 > 4i32;
    let lt = 4i32 < 5i32;
    let gte = 5i32 >= 4i32;
    let lte = 4i32 <= 5i32;

    let unary_not = !true;
    let unary_minus = -5i32;
    let unary_bitflip = !5i32;
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_i32(0);
    eval.set_i32(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "()");
    Ok(())
}

#[test]
fn compile_const() -> Result<(), Error> {
    let prg = "
const MY_CONST: u16 = PARTY_0::MY_CONST;
pub fn main(x: u16) -> u16 {
    x + MY_CONST
}
";
    let consts = HashMap::from_iter(vec![(
        "PARTY_0".to_string(),
        HashMap::from_iter(vec![(
            "MY_CONST".to_string(),
            Literal::NumUnsigned(2, UnsignedNumType::U16),
        )]),
    )]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        257
    );
    Ok(())
}

#[test]
fn compile_const_literal() -> Result<(), Error> {
    let prg = "
const MY_CONST: u16 = 2u16;
pub fn main(x: u16) -> u16 {
    x + MY_CONST
}
";
    let consts = HashMap::from_iter(vec![]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        257
    );
    Ok(())
}

#[test]
fn compile_const_usize() -> Result<(), Error> {
    let prg = "
const MY_CONST: usize = PARTY_0::MY_CONST;
pub fn main(x: u16) -> u16 {
    let array = [2u16; MY_CONST];
    x + array[1]
}
";
    let consts = HashMap::from_iter(vec![(
        "PARTY_0".to_string(),
        HashMap::from_iter(vec![(
            "MY_CONST".to_string(),
            Literal::NumUnsigned(2, UnsignedNumType::Usize),
        )]),
    )]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        257
    );
    Ok(())
}

#[test]
fn compile_const_aggregated_max() -> Result<(), Error> {
    let prg = "
const MY_CONST: usize = max(PARTY_0::MY_CONST, PARTY_1::MY_CONST);
pub fn main(x: u16) -> u16 {
    let array = [2u16; MY_CONST];
    x + array[1]
}
";
    let consts = HashMap::from_iter(vec![
        (
            "PARTY_0".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(1, UnsignedNumType::Usize),
            )]),
        ),
        (
            "PARTY_1".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(2, UnsignedNumType::Usize),
            )]),
        ),
    ]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        257
    );
    Ok(())
}

#[test]
fn compile_const_aggregated_min() -> Result<(), Error> {
    let prg = "
const MY_CONST: usize = min(PARTY_0::MY_CONST, PARTY_1::MY_CONST);
pub fn main(x: u16) -> u16 {
    let array = [2u16; MY_CONST];
    x + array[1]
}
";
    let consts = HashMap::from_iter(vec![
        (
            "PARTY_0".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(3, UnsignedNumType::Usize),
            )]),
        ),
        (
            "PARTY_1".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(2, UnsignedNumType::Usize),
            )]),
        ),
    ]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(255);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        257
    );
    Ok(())
}

#[test]
fn compile_const_size_in_fn_param() -> Result<(), Error> {
    let prg = "
const MY_CONST: usize = max(PARTY_0::MY_CONST, PARTY_1::MY_CONST);
pub fn main(array: [u16; MY_CONST]) -> u16 {
    array[1]
}
";
    let consts = HashMap::from_iter(vec![
        (
            "PARTY_0".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(1, UnsignedNumType::Usize),
            )]),
        ),
        (
            "PARTY_1".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(2, UnsignedNumType::Usize),
            )]),
        ),
    ]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.parse_literal("[7u16, 8u16]").unwrap();
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(u16::try_from(output).map_err(|e| pretty_print(e, prg))?, 8);
    Ok(())
}

#[test]
fn compile_const_size_for_each_loop() -> Result<(), Error> {
    let prg = "
const MY_CONST: usize = max(PARTY_0::MY_CONST, PARTY_1::MY_CONST);
pub fn main(array: [u16; MY_CONST]) -> u16 {
    let mut result = 0u16;
    for elem in array {
        result = result + elem;
    }
    result
}
";
    let consts = HashMap::from_iter(vec![
        (
            "PARTY_0".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(1, UnsignedNumType::Usize),
            )]),
        ),
        (
            "PARTY_1".to_string(),
            HashMap::from_iter(vec![(
                "MY_CONST".to_string(),
                Literal::NumUnsigned(2, UnsignedNumType::Usize),
            )]),
        ),
    ]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.parse_literal("[7u16, 8u16]").unwrap();
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(u16::try_from(output).map_err(|e| pretty_print(e, prg))?, 15);
    Ok(())
}

#[test]
fn compile_join_fn() -> Result<(), Error> {
    let prg = "
pub fn main(rows1: [([u8; 3], u16); 4], rows2: [([u8; 3], u16, u16); 3]) -> u16 {
    let mut result = 0u16;
    for row in join(rows1, rows2) {
        let ((_, field1), (_, field2, field3)) = row;
        result = result + field1 + field2 + field3;
    }
    result
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    let id_aaa = Literal::Array(vec![
        Literal::NumUnsigned(97, UnsignedNumType::U8),
        Literal::NumUnsigned(97, UnsignedNumType::U8),
        Literal::NumUnsigned(97, UnsignedNumType::U8),
    ]);
    let id_bar = Literal::Array(vec![
        Literal::NumUnsigned(98, UnsignedNumType::U8),
        Literal::NumUnsigned(97, UnsignedNumType::U8),
        Literal::NumUnsigned(114, UnsignedNumType::U8),
    ]);
    let id_baz = Literal::Array(vec![
        Literal::NumUnsigned(98, UnsignedNumType::U8),
        Literal::NumUnsigned(97, UnsignedNumType::U8),
        Literal::NumUnsigned(122, UnsignedNumType::U8),
    ]);
    let id_foo = Literal::Array(vec![
        Literal::NumUnsigned(102, UnsignedNumType::U8),
        Literal::NumUnsigned(111, UnsignedNumType::U8),
        Literal::NumUnsigned(111, UnsignedNumType::U8),
    ]);
    let id_qux = Literal::Array(vec![
        Literal::NumUnsigned(113, UnsignedNumType::U8),
        Literal::NumUnsigned(117, UnsignedNumType::U8),
        Literal::NumUnsigned(120, UnsignedNumType::U8),
    ]);
    eval.set_literal(Literal::Array(vec![
        Literal::Tuple(vec![
            id_aaa.clone(),
            Literal::NumUnsigned(0, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            id_bar.clone(),
            Literal::NumUnsigned(1, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            id_baz.clone(),
            Literal::NumUnsigned(2, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            id_qux.clone(),
            Literal::NumUnsigned(3, UnsignedNumType::U16),
        ]),
    ]))
    .unwrap();
    eval.set_literal(Literal::Array(vec![
        Literal::Tuple(vec![
            id_baz.clone(),
            Literal::NumUnsigned(4, UnsignedNumType::U16),
            Literal::NumUnsigned(5, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            id_foo.clone(),
            Literal::NumUnsigned(6, UnsignedNumType::U16),
            Literal::NumUnsigned(7, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            id_qux.clone(),
            Literal::NumUnsigned(8, UnsignedNumType::U16),
            Literal::NumUnsigned(9, UnsignedNumType::U16),
        ]),
    ]))
    .unwrap();
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 3 + 4 + 5 + 8 + 9
    );
    Ok(())
}
