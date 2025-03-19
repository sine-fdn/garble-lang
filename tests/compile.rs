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
    x + {y}
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
    x + {y}
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
    let y = x + 1;
    y + 1
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
    add(x, 1)
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
        100
    } else {
        50
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
    x | (y & (z ^ 2))
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
    (x > y) & (x < 10)
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
    (x == y) & (x != 0)
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
        for shifts in 0..(u16::BITS as u8 - 1) {
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
    x | (y & (z ^ 2))
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
            let expected = x > y;
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
    let test_values = (-20..20).chain(vec![i16::MAX, i16::MIN]);
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
    x + -10
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
    arr[i] = x * 2;
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
pub fn main(x: i32) -> i32 {{
    let mut arr = [x; {array_size}];
    let mut acc = 0;
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
        eval.set_i32(x);
        let output = eval.run().map_err(|e| pretty_print(e, prg))?;
        assert_eq!(
            i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
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
    for j in 0..{array_size} {{
        arr[j] = arr[j] * 2;
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
pub fn main(_x: u8) -> i32 {
    let arr = 1..101;
    let mut acc = 0;
    for i in arr {{
        acc = acc + i as i32;
    }}
    acc
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u8(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        i32::try_from(output).map_err(|e| pretty_print(e, prg))?,
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
    let t = (-3, -2i16, -1i8, true, false);
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
            3 => assert!(bool::try_from(output).map_err(|e| pretty_print(e, prg))?),
            4 => assert!(!(bool::try_from(output).map_err(|e| pretty_print(e, prg))?)),
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
        Foobar::Bar(6)
    } else {
        Foobar::Foo
    };
    match choice {
        Foobar::Foo => 5,
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
    let op = if choice == 0 {
        Ops::Mul(x, y)
    } else {
        Ops::Div(x, y)
    };

    match op {
        Ops::Div(x, 0) => 42,
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
        0..10 => 1,
        10 => 2,
        11 => 2,
        13 => 2,
        12..100 => 2,
        100..=255 => 3,
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
    let x = (false, x, -5);
    match x {
        (true, x, y) => 1,
        (false, 0, y) => 2,
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
    let x = (x, (x * 2, 1u8));
    match x {
        (0, _) => 1,
        (1..=255, (x_twice, 1)) => x_twice,
        (1..=255, (_, 1..=255)) => 2,
        (1..=255, (_, 0)) => 3,
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
    (values.0 + 1, values.1 + 1)
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "(2, 3)")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(format!("{r}"), "(3, 4)");
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
        Op::Div(x, 0) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "Op::Div(10, 2)")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "OpResult::Ok(5)");
    Ok(())
}

#[test]
fn compile_array_literal_access() -> Result<(), Error> {
    let prg = "
pub fn main(i: usize) -> i32 {
    [-2, -1, 0, 1, 2][i]
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
pub fn main(nums: [u8; 5], init: u16) -> [u8; 5] {
    let mut sum = init;
    for n in nums {
        sum = sum + n as u16;
    }
    let mut nums = [0u8; 5];
    for i in 0..5 {
        nums[i] = sum as u8;
    }
    nums
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "[1, 2, 3, 4, 5]")?;
    eval.set_literal(input.as_literal())?;
    eval.set_u16(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "[15, 15, 15, 15, 15]");
    Ok(())
}

#[test]
fn compile_if_elseif_else() -> Result<(), Error> {
    let prg = "
pub fn main(x: i8) -> i8 {
    if x < 0 {
        -1
    } else if x == 0 {
        0
    } else {
        1
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
      let mut points = 0;

      if income >= 10000 {
        points = points + 200
      } else if income >= 2000 {
        points = points + 50
      } else {
        points = points + 0
      }

      if points > 150 {
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
    let y = x + 1;
    let z = {
        let y = x + 10;
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
    let foobar = FooBar { foo: x, bar: 2 };
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
        FooBarBaz { foo: 1, bar: 0, baz: false } => FooBarBaz { baz: true, foo: 1, bar: 1 },
        FooBarBaz { foo: 1, baz, bar: 0 } => FooBarBaz { foo: 1, bar: 1, baz },
        FooBarBaz { bar, baz: false, foo } => FooBarBaz { foo, bar, baz: true },
        FooBarBaz { foo, bar, baz } => FooBarBaz { foo, bar: 1, baz },
        FooBarBaz { foo, .. } => FooBarBaz { foo, bar: 1, baz: true },
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;

    let mut eval = compiled.evaluator();
    let input = compiled.parse_arg(0, "FooBarBaz { foo: 1, bar: 0, baz: true }")?;
    eval.set_literal(input.as_literal())?;
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "FooBarBaz {bar: 1, baz: true, foo: 1}");
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
    x + /* ... */ 1
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

    let bar = (0, 0);
    let foobar = FooBar { foo: 0, bar };
    let FooBar { bar, .. } = foobar;
    let (y, z) = bar;
    a + y
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_literal(compiled.parse_arg(0, "(1, 2)")?.as_literal())?;
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
        FooBar { foo: 0, .. } => 1,
        FooBar { foo, .. } => foo,
    }
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_literal(compiled.parse_arg(0, "(2, 3)")?.as_literal())?;
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
        foo: 1,
        bar: (2, 3),
        baz: (4, 5, 6),
    };
    match x {
        0 => {
            let FooBar { foo, .. } = foobar;
            foo
        },
        1 => {
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
    let mut y = 0;
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
    let mut y = 0;
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
    let mut y = 0;
    match x {
        0 => {},
        1..10 => {
            y = 1;
        },
        10..100 => {
            y = 2;
        },
        _ => {
            y = 3;
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
    for i in 0..10 {
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
    let mut sum = 0;
    for i in [2, 4, 6, 8] {
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
    let mut array = [0; 5];
    for i in 0..5 {
        array[i as usize] = i as i32 * 2;
    }
    array
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_i32(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "[0, 2, 4, 6, 8]");
    Ok(())
}

#[test]
fn compile_arrays_copied_by_value() -> Result<(), Error> {
    let prg = "
pub fn main(replacement: i32) -> [i32; 4] {
    let mut array1 = [10, 20, 30, 40];
    let second_val = array1[1]; // will be `20`
    let mut array2 = array1;
    array2[1] = replacement;
    let second_val1 = array1[1]; // will still be `20`
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
        assert_eq!(r.to_string(), format!("[10, {x}, 30, 40]"));
    }
    Ok(())
}

#[test]
fn compile_operator_examples() -> Result<(), Error> {
    let prg = "
pub fn main(_a: i32, _b: i32) -> () {
    let add = 0 + 1;
    let sub = 1 - 1;
    let mul = 2 * 1;
    let div = 2 / 1;
    let rem = 5 % 2;

    let bit_xor = 4 ^ 6;
    let bit_and = 4 & 6;
    let bit_or = 4 | 6;
    let bit_shiftl = 4 << 1;
    let bit_shiftr = 4 >> 1;

    let and = true & false;
    let or = true | false;

    let eq = true == false;
    let neq = true != false;

    let gt = 5 > 4;
    let lt = 4 < 5;
    let gte = 5 >= 4;
    let lte = 4 <= 5;

    let unary_not = !true;
    let unary_minus = -5;
    let unary_bitflip = !5;
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
fn compile_or_xor() -> Result<(), Error> {
    let prg = "
pub fn main(a: bool, b: bool, c: bool) -> bool {
    (a & b) | (a & c)
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    for a in [true, false] {
        for b in [true, false] {
            for c in [true, false] {
                let mut eval = compiled.evaluator();
                eval.set_bool(a);
                eval.set_bool(b);
                eval.set_bool(c);
                let output = eval.run().map_err(|e| pretty_print(e, prg))?;
                assert_eq!(
                    bool::try_from(output).map_err(|e| pretty_print(e, prg))?,
                    (a & b) | (a & c),
                    "({a} & {b}) | ({a} & {c})"
                );
            }
        }
    }
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
    let array = [2; MY_CONST];
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
    let array = [2; MY_CONST];
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
    let array = [2; MY_CONST];
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
pub fn main(array: [u16; MY_CONST], _: u8) -> u16 {
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
    eval.parse_literal("[7, 8]").unwrap();
    eval.set_u8(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(u16::try_from(output).map_err(|e| pretty_print(e, prg))?, 8);
    Ok(())
}

#[test]
fn compile_const_size_for_each_loop() -> Result<(), Error> {
    let prg = "
const MY_CONST: usize = max(PARTY_0::MY_CONST, PARTY_1::MY_CONST);
pub fn main(array: [u16; MY_CONST], _: u8) -> u16 {
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
    eval.parse_literal("[7, 8]").unwrap();
    eval.set_u8(0);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(u16::try_from(output).map_err(|e| pretty_print(e, prg))?, 15);
    Ok(())
}

#[test]
fn compile_join_loop() -> Result<(), Error> {
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

#[test]
fn compile_multiple_join_loops() -> Result<(), Error> {
    for joined in 0..4 {
        for only_a in 0..4 {
            for only_b in 1..4 {
                println!("Testing join loops for {joined} / {only_a} / {only_b} elements");
                let a = joined + only_a;
                let b = joined + only_b;
                let prg = format!(
                    "
pub fn main(rows1: [(u8, u16); {a}], rows2: [(u8, u16, u16); {b}]) -> u16 {{
    let mut result = 0u16;
    for row in join(rows1, rows2) {{
        let ((_, field1), (_, field2, field3)) = row;
        result = result + field1 + field2 + field3;
    }}
    result
}}
"
                );
                let compiled = compile(&prg).map_err(|e| pretty_print(e, &prg))?;
                compiled.circuit.validate().unwrap();
                let mut eval = compiled.evaluator();
                let mut rows_a = vec![];
                let mut rows_b = vec![];
                for i in 0..joined {
                    rows_a.push(Literal::Tuple(vec![
                        Literal::NumUnsigned(i, UnsignedNumType::U8),
                        Literal::NumUnsigned(2, UnsignedNumType::U16),
                    ]));
                    rows_b.push(Literal::Tuple(vec![
                        Literal::NumUnsigned(i, UnsignedNumType::U8),
                        Literal::NumUnsigned(1, UnsignedNumType::U16),
                        Literal::NumUnsigned(1, UnsignedNumType::U16),
                    ]));
                }
                for i in joined..joined + only_a {
                    rows_a.push(Literal::Tuple(vec![
                        Literal::NumUnsigned(i, UnsignedNumType::U8),
                        Literal::NumUnsigned(2, UnsignedNumType::U16),
                    ]));
                }
                for i in joined + only_a..joined + only_a + only_b {
                    rows_b.push(Literal::Tuple(vec![
                        Literal::NumUnsigned(i, UnsignedNumType::U8),
                        Literal::NumUnsigned(1, UnsignedNumType::U16),
                        Literal::NumUnsigned(1, UnsignedNumType::U16),
                    ]));
                }
                eval.set_literal(Literal::Array(rows_a)).unwrap();
                eval.set_literal(Literal::Array(rows_b)).unwrap();
                let output = eval.run().map_err(|e| pretty_print(e, &prg))?;
                assert_eq!(
                    u16::try_from(output).map_err(|e| pretty_print(e, &prg))?,
                    joined as u16 * 4
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_add_assign() -> Result<(), Error> {
    let prg = "
pub fn main(a: u32) -> u32 {
    let mut x = 3u32;
    x += a;
    x += 2;
    x
}";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u32(10);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    let r = output.into_literal().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(r.to_string(), "15");
    Ok(())
}

#[test]
fn compile_operator_assignment_examples() -> Result<(), Error> {
    let prg = "
pub fn main(_a: i32, _b: i32) -> () {
    let mut x = 0i32;
    x += 5;
    x -= 3;
    x *= 3;
    x /= 2;
    x %= 1;

    let mut x = 0u32;
    x ^= 4;
    x &= 3;
    x |= 2;
    x <<= 1;
    x >>= 1;

    let mut b = true;
    b ^= true;
    b &= true;
    b |= true;
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
fn compile_join_loop_destructuring() -> Result<(), Error> {
    let prg = "
pub fn main(rows1: [(u8, u16); 3], rows2: [(u8, u16); 3]) -> u16 {
    let mut result = 0u16;
    for ((_, a), (_, b)) in join(rows1, rows2) {
        result += a + b;
    }
    result
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_literal(Literal::Array(vec![
        Literal::Tuple(vec![
            Literal::NumUnsigned(1, UnsignedNumType::U8),
            Literal::NumUnsigned(2, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            Literal::NumUnsigned(2, UnsignedNumType::U8),
            Literal::NumUnsigned(4, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            Literal::NumUnsigned(3, UnsignedNumType::U8),
            Literal::NumUnsigned(6, UnsignedNumType::U16),
        ]),
    ]))
    .unwrap();
    eval.set_literal(Literal::Array(vec![
        Literal::Tuple(vec![
            Literal::NumUnsigned(1, UnsignedNumType::U8),
            Literal::NumUnsigned(2, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            Literal::NumUnsigned(2, UnsignedNumType::U8),
            Literal::NumUnsigned(4, UnsignedNumType::U16),
        ]),
        Literal::Tuple(vec![
            Literal::NumUnsigned(4, UnsignedNumType::U8),
            Literal::NumUnsigned(8, UnsignedNumType::U16),
        ]),
    ]))
    .unwrap();
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 2 + 4 + 4
    );
    Ok(())
}

#[test]
fn compile_for_loop_destructuring() -> Result<(), Error> {
    let prg = "
pub fn main(_x: i32) -> i32 {
    let mut sum = 0i32;
    for (a, b) in [(2, 4), (6, 8)] {
        sum += a + b;
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
fn compile_single_array_as_3_parties() -> Result<(), Error> {
    let prg = "
pub fn main(parties: [u32; 3]) -> u32 {
  parties[0] + parties[1] + parties[2]
}";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u32(2);
    eval.set_u32(4);
    eval.set_u32(6);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u32::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6,
    );
    Ok(())
}

#[test]
fn compile_single_array_as_4_parties() -> Result<(), Error> {
    let prg = "
pub fn main(parties: [u32; 4]) -> u32 {
  let mut result = 0u32;
  for p in parties {
    result += p
  }
  result
}";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u32(2);
    eval.set_u32(4);
    eval.set_u32(6);
    eval.set_u32(8);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u32::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6 + 8,
    );
    Ok(())
}

#[test]
fn compile_single_array_with_const_size_as_multiple_parties() -> Result<(), Error> {
    let prg = "
const PARTIES: usize = PARTIES::TOTAL;
pub fn main(array: [u16; PARTIES]) -> u16 {
    let mut result = 0u16;
    for elem in array {
        result = result + elem;
    }
    result
}
";
    let consts = HashMap::from_iter(vec![(
        "PARTIES".to_string(),
        HashMap::from_iter(vec![(
            "TOTAL".to_string(),
            Literal::NumUnsigned(3, UnsignedNumType::Usize),
        )]),
    )]);
    let compiled = compile_with_constants(prg, consts).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(4);
    eval.set_u16(6);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6
    );
    Ok(())
}

#[test]
fn compile_type_declaration_in_let() -> Result<(), Error> {
    let prg = "
pub fn main(a: u16, b: u16) -> u16 {
    let c: u16 = 6;
    a + b + c
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(4);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6
    );
    Ok(())
}

#[test]
fn compile_type_declaration_in_let_mut() -> Result<(), Error> {
    let prg = "
pub fn main(a: u16, b: u16) -> u16 {
    let mut result: u16 = 6;
    result += a + b;
    result
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(4);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6
    );
    Ok(())
}

#[test]
fn compile_array_assign_via_index() -> Result<(), Error> {
    let prg = "
pub fn main(a: u16, b: u16) -> u16 {
    let mut result: [u16; 2] = [3, 3];
    result[0] += a;
    result[1] += b;
    result[0] + result[1]
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(4);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 3 + 3
    );
    Ok(())
}

#[test]
fn compile_array_assign_via_nested_index() -> Result<(), Error> {
    let prg = "
pub fn main(a: u16, b: u16) -> u16 {
    let mut result: [[u16; 3]; 2] = [[1u16, 2u16, 3u16], [4u16, 5u16, 6u16]];
    result[1][2] += a;
    result[1][2] += b;
    result[1][2]
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(4);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6
    );
    Ok(())
}

#[test]
fn compile_tuple_assign() -> Result<(), Error> {
    let prg = "
pub fn main(a: u16, b: u16) -> u16 {
    let mut t: (u16, u16) = (0, 2);
    t.1 += a;
    t.1 += b;
    t.1
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(4);
    eval.set_u16(6);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4 + 6
    );
    Ok(())
}

#[test]
fn compile_struct_assign() -> Result<(), Error> {
    let prg = "
struct Foo {
  foo: u16
}
pub fn main(a: u16, b: u16) -> u16 {
    let mut f = Foo { foo: 0 };
    f.foo += a;
    f.foo += b;
    f.foo
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(4);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        2 + 4
    );
    Ok(())
}

#[test]
fn compile_tuple_and_struct_assign_via_nested_index() -> Result<(), Error> {
    let prg = "
struct Foo {
  foo: u16
}
pub fn main(a: u16, b: u16) -> u16 {
    let mut result: [(u16, Foo); 2] = [(1, Foo { foo: 2 }), (1, Foo { foo: 4 })];
    result[1].0 += a;
    result[1].1.foo += b;
    result[1].0 + result[1].1.foo
}
";
    let compiled = compile(prg).map_err(|e| pretty_print(e, prg))?;
    let mut eval = compiled.evaluator();
    eval.set_u16(2);
    eval.set_u16(6);
    let output = eval.run().map_err(|e| pretty_print(e, prg))?;
    assert_eq!(
        u16::try_from(output).map_err(|e| pretty_print(e, prg))?,
        1 + 2 + 4 + 6
    );
    Ok(())
}
