use garble::{ast::Type, check, compile, eval::Evaluator, io::Literal};

#[test]
fn compile_xor() -> Result<(), String> {
    for y in [true, false] {
        let prg = format!(
            "
fn main(x: bool) -> bool {{
    x ^ {}
}}
",
            y
        );
        let circuit = compile(&prg).map_err(|e| e.prettify(&prg))?;
        let mut eval: Evaluator = circuit.into();
        for x in [true, false] {
            eval.set_bool(x);
            eval.run().map_err(|e| e.prettify(&prg))?;
            assert_eq!(eval.get_bool().map_err(|e| e.prettify(&prg))?, x ^ y);
        }
    }
    Ok(())
}

#[test]
fn compile_add() -> Result<(), String> {
    for y in 0..127 {
        let prg = format!(
            "
fn main(x: u8) -> u8 {{
    x + {}
}}
",
            y
        );
        let circuit = compile(&prg).map_err(|e| e.prettify(&prg))?;
        let mut eval: Evaluator = circuit.into();
        for x in 0..127 {
            eval.set_u8(x);
            eval.run().map_err(|e| e.prettify(&prg))?;
            assert_eq!(eval.get_u8().map_err(|e| e.prettify(&prg))?, x + y);
        }
    }
    Ok(())
}

#[test]
fn compile_add_with_int_coercion() -> Result<(), String> {
    for y in 240..280 {
        let prg = format!(
            "
fn main(x: u16) -> u16 {{
    x + {}
}}
",
            y
        );
        let circuit = compile(&prg).map_err(|e| e.prettify(&prg))?;
        let mut eval: Evaluator = circuit.into();
        for x in 240..280 {
            eval.set_u16(x);
            eval.run().map_err(|e| e.prettify(&prg))?;
            assert_eq!(eval.get_u16().map_err(|e| e.prettify(&prg))?, x + y);
        }
    }
    Ok(())
}

#[test]
fn compile_let_expr() -> Result<(), String> {
    let prg = "
fn main(x: u16) -> u16 {
    let y = x + 1;
    y + 1
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    eval.set_u16(255);
    eval.run().map_err(|e| e.prettify(prg))?;
    assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, 257);
    Ok(())
}

#[test]
fn compile_static_fn_defs() -> Result<(), String> {
    let prg = "
fn main(x: u16) -> u16 {
    inc(x)
}

fn inc(x: u16) -> u16 {
    add(x, 1)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    eval.set_u16(255);
    eval.run().map_err(|e| e.prettify(prg))?;
    assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, 256);
    Ok(())
}

#[test]
fn compile_if() -> Result<(), String> {
    let prg = "
fn main(x: bool) -> u8 {
    if (true & false) ^ x {
        100
    } else {
        50
    }
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for b in [true, false] {
        let expected = if b { 100 } else { 50 };
        eval.set_bool(b);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, expected);
    }
    Ok(())
}

#[test]
fn compile_bit_ops_for_numbers() -> Result<(), String> {
    let prg = "
fn main(x: u16, y: u16, z: u16) -> u16 {
    x | (y & (z ^ 2))
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 10..20 {
        for y in 10..20 {
            for z in 10..20 {
                let expected = x | (y & (z ^ 2));
                eval.set_u16(x);
                eval.set_u16(y);
                eval.set_u16(z);
                eval.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, expected);
            }
        }
    }
    Ok(())
}

#[test]
fn compile_greater_than_and_less_than() -> Result<(), String> {
    let prg = "
fn main(x: u16, y: u16) -> bool {
    (x > y) & (x < 10)
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 5..15 {
        for y in 5..15 {
            let expected = (x > y) && (x < 10);
            eval.set_u16(x);
            eval.set_u16(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_bool().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_equals_and_not_equals() -> Result<(), String> {
    let prg = "
fn main(x: u16, y: u16) -> bool {
    (x == y) & (x != 0)
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 0..2 {
        for y in 0..2 {
            let expected = (x == y) && (x != 0);
            eval.set_u16(x);
            eval.set_u16(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_bool().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_casts() -> Result<(), String> {
    let prg = "
fn main(x: u16, y: u8) -> u16 {
    (x as u8) as u16 + y as u16
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 200..300 {
        for y in 0..10 {
            let expected = (x as u8) as u16 + y as u16;
            eval.set_u16(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_bool_casts() -> Result<(), String> {
    let prg = "
fn main(x: bool, y: u8) -> u16 {
    x as u16 + y as u16
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in [true, false] {
        for y in 0..10 {
            let expected = (x as u16) + (y as u16);
            eval.set_bool(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_bit_shifts() -> Result<(), String> {
    let prg = "
fn main(mode: bool, x: u16, y: u8) -> u16 {
    if mode { x << y } else { x >> y }
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for mode in [true, false] {
        for x in 240..270 {
            for y in 0..20 {
                let expected = if y >= 16 {
                    0
                } else if mode {
                    x << y
                } else {
                    x >> y
                };
                eval.set_bool(mode);
                eval.set_u16(x);
                eval.set_u8(y);
                eval.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, expected);
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_nums() -> Result<(), String> {
    let prg = "
fn main(x: i8) -> i8 {
    x
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -128..127 {
        eval.set_i8(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x);
    }
    Ok(())
}

#[test]
fn compile_signed_add() -> Result<(), String> {
    let prg = "
fn main(x: i8, y: i8) -> i8 {
    x + y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -64..64 {
        for y in -64..63 {
            eval.set_i8(x);
            eval.set_i8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x + y);
        }
    }
    Ok(())
}

#[test]
fn compile_bit_ops_for_signed_numbers() -> Result<(), String> {
    let prg = "
fn main(x: i16, y: i16, z: i16) -> i16 {
    x | (y & (z ^ 2))
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        for y in -10..10 {
            for z in -10..10 {
                let expected = x | (y & (z ^ 2));
                eval.set_i16(x);
                eval.set_i16(y);
                eval.set_i16(z);
                eval.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, expected);
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_greater_than_and_less_than() -> Result<(), String> {
    let prg = "
fn main(x: i16, y: i16) -> bool {
    (x > y) & (y < x)
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        for y in -10..10 {
            let expected = (x > y) && (y < x);
            eval.set_i16(x);
            eval.set_i16(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_bool().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_bit_shifts() -> Result<(), String> {
    let prg = "
fn main(mode: bool, x: i16, y: u8) -> i16 {
    if mode {
        x << y
    } else {
        x >> y
    }
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for mode in [true, false] {
        for x in -20..20 {
            for y in 0..20 {
                // TODO: how do we want to handle overflows?
                let expected = if y >= 16 && !mode && x < 0 {
                    // shift right of signed num with overflow:
                    -1
                } else if y >= 16 {
                    // shift with overflow:
                    0
                } else if mode {
                    x << y
                } else {
                    x >> y
                };
                eval.set_bool(mode);
                eval.set_i16(x);
                eval.set_u8(y);
                eval.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, expected);
            }
        }
    }
    Ok(())
}

#[test]
fn compile_add_with_signed_int_coercion() -> Result<(), String> {
    let prg = "
fn main(x: i16) -> i16 {
    x + -10
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        let expected = x + -10;
        eval.set_i16(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, expected);
    }
    Ok(())
}

#[test]
fn compile_sub() -> Result<(), String> {
    let prg = "
fn main(x: i16, y: i16) -> i16 {
    x - y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..20 {
        for y in -10..256 {
            eval.set_i16(x);
            eval.set_i16(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, x - y);
        }
    }
    Ok(())
}

#[test]
fn compile_unary_negation() -> Result<(), String> {
    let prg = "
fn main(x: i16) -> i16 {
    -x
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -127..127 {
        eval.set_i16(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, -x);
    }
    Ok(())
}

#[test]
fn compile_unary_not() -> Result<(), String> {
    let prg = "
fn main(x: i16) -> i16 {
    !x
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -127..127 {
        eval.set_i16(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, !x);
    }

    let prg = "
fn main(x: bool) -> bool {
    !x
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for b in [true, false] {
        eval.set_bool(b);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_bool().map_err(|e| e.prettify(prg))?, !b);
    }
    Ok(())
}

#[test]
fn compile_unsigned_mul() -> Result<(), String> {
    let prg = "
fn main(x: u16, y: u16) -> u16 {
    x * y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 0..20 {
        for y in 250..300 {
            eval.set_u16(x);
            eval.set_u16(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u16().map_err(|e| e.prettify(prg))?, x * y);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_mul() -> Result<(), String> {
    let prg = "
fn main(x: i16, y: i16) -> i16 {
    x * y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        for y in -10..10 {
            eval.set_i16(x);
            eval.set_i16(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, x * y);
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_div() -> Result<(), String> {
    let prg = "
fn main(x: u8, y: u8) -> u8 {
    x / y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 0..255 {
        for y in 1..10 {
            eval.set_u8(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, x / y);
        }
        for y in 250..255 {
            eval.set_u8(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, x / y);
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_mod() -> Result<(), String> {
    let prg = "
fn main(x: u8, y: u8) -> u8 {
    x % y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in 0..255 {
        for y in 1..10 {
            eval.set_u8(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, x % y);
        }
        for y in 250..255 {
            eval.set_u8(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, x % y);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_div() -> Result<(), String> {
    let prg = "
fn main(x: i8, y: i8) -> i8 {
    x / y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -128..127 {
        for y in -4..5 {
            if y == -1 || y == 0 {
                continue;
            }
            eval.set_i8(x);
            eval.set_i8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x / y);
        }
        for y in 120..127 {
            eval.set_i8(x);
            eval.set_i8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x / y);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_mod() -> Result<(), String> {
    let prg = "
fn main(x: i8, y: i8) -> i8 {
    x % y
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -128..127 {
        for y in -4..5 {
            if y == -1 || y == 0 {
                continue;
            }
            eval.set_i8(x);
            eval.set_i8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x % y);
        }
        for y in 120..127 {
            eval.set_i8(x);
            eval.set_i8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x % y);
        }
    }
    Ok(())
}

#[test]
fn compile_array_repeat_literal_access() -> Result<(), String> {
    let array_size = 256;
    let prg = &format!(
        "
fn main(x: i8, i: usize) -> i8 {{
    [x; {}][i]
}}
",
        array_size
    );
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        for i in 0..array_size {
            eval.set_i8(x);
            eval.set_usize(i);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x);
        }
    }
    Ok(())
}

#[test]
fn compile_array_assignment() -> Result<(), String> {
    let array_size = 8;
    let prg = &format!(
        "
fn main(x: i8, i: usize, j: usize) -> i8 {{
    let arr = [x; {}];
    let arr = arr.update(i, x * 2);
    arr[j]
}}
",
        array_size
    );
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    let x = -5;
    for i in 0..array_size {
        for j in 0..array_size {
            let expected = if i == j { x * 2 } else { x };
            eval.set_i8(x);
            eval.set_usize(i);
            eval.set_usize(j);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_fold() -> Result<(), String> {
    let array_size = 8;
    let prg = &format!(
        "
fn main(x: i8) -> i8 {{
    let arr = [x; {}];
    arr.fold(0, |acc: i8, x: i8| -> i8 {{
        acc + x
    }})
}}
",
        array_size
    );
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        eval.set_i8(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, array_size * x);
    }
    Ok(())
}

#[test]
fn compile_map() -> Result<(), String> {
    let array_size = 8;
    let prg = &format!(
        "
fn main(x: i8, i: usize) -> i8 {{
    let arr = [x; {}];
    let arr = arr.map(|x: i8| -> i8 {{x * 2}});
    arr[i]
}}
",
        array_size
    );
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for x in -10..10 {
        for i in 0..array_size {
            eval.set_i8(x);
            eval.set_usize(i);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, x * 2);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_casts() -> Result<(), String> {
    // signed to unsigned:

    let prg = "fn main(x: i16) -> u8 { x as u8 }";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut comp: Evaluator = circuit.into();
    for x in -200..200 {
        comp.set_i16(x);
        comp.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(comp.get_u8().map_err(|e| e.prettify(prg))?, x as u8);
    }

    let prg = "fn main(x: i8) -> u16 { x as u16 }";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut comp: Evaluator = circuit.into();
    for x in -128..127 {
        comp.set_i8(x);
        comp.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(comp.get_u16().map_err(|e| e.prettify(prg))?, x as u16);
    }

    // unsigned to signed:

    let prg = "fn main(x: u16) -> i8 { x as i8 }";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut comp: Evaluator = circuit.into();
    for x in 200..300 {
        comp.set_u16(x);
        comp.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(comp.get_i8().map_err(|e| e.prettify(prg))?, x as i8);
    }

    let prg = "fn main(x: u8) -> i16 { x as i16 }";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut comp: Evaluator = circuit.into();
    for x in 200..255 {
        comp.set_u8(x);
        comp.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(comp.get_i16().map_err(|e| e.prettify(prg))?, x as i16);
    }

    // signed to signed:

    let prg = "fn main(x: i16) -> i8 { x as i8 }";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut comp: Evaluator = circuit.into();
    for x in -200..200 {
        comp.set_i16(x);
        comp.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(comp.get_i8().map_err(|e| e.prettify(prg))?, x as i8);
    }

    let prg = "fn main(x: i8) -> i16 { x as i16 }";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut comp: Evaluator = circuit.into();
    for x in -128..127 {
        comp.set_i8(x);
        comp.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(comp.get_i16().map_err(|e| e.prettify(prg))?, x as i16);
    }
    Ok(())
}

#[test]
fn compile_range() -> Result<(), String> {
    let prg = "
fn main(_x: u8) -> i16 {
    let arr = 1..101;
    arr.fold(0, |acc: i16, x: usize| -> i16 {
        acc + (x as i16)
    })
}
";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    eval.set_u8(0);
    eval.run().map_err(|e| e.prettify(prg))?;
    assert_eq!(eval.get_i16().map_err(|e| e.prettify(prg))?, 50 * 101);
    Ok(())
}

#[test]
fn compile_tuple() -> Result<(), String> {
    for (t, i) in [("i8", 0), ("i8", 1), ("i8", 2), ("bool", 3), ("bool", 4)] {
        let prg = &format!(
            "
fn main(x: bool) -> {} {{
    let t = (-3, -2, -1, true, false);
    t.{}
}}
",
            t, i
        );
        let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
        let mut eval: Evaluator = circuit.into();
        eval.set_bool(false);
        eval.run().map_err(|e| e.prettify(prg))?;
        if i <= 2 {
            assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, i - 3);
        } else if i == 3 {
            assert_eq!(eval.get_bool().map_err(|e| e.prettify(prg))?, true);
        } else if i == 4 {
            assert_eq!(eval.get_bool().map_err(|e| e.prettify(prg))?, false);
        }
    }
    Ok(())
}

#[test]
fn compile_exhaustive_bool_pattern() -> Result<(), String> {
    let prg = "
enum Foobar {
    Foo,
    Bar(bool, bool),
}

fn main(b: bool) -> u8 {
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
        let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
        let mut eval: Evaluator = circuit.into();
        eval.set_bool(b);
        eval.run().map_err(|e| e.prettify(prg))?;
        let result = eval.get_u8().map_err(|e| e.prettify(prg))?;
        if b {
            assert_eq!(result, 3);
        } else {
            assert_eq!(result, 5);
        }
    }
    Ok(())
}

#[test]
fn compile_exhaustive_enum_pattern() -> Result<(), String> {
    let prg = "
enum Foobar {
    Foo,
    Bar(u8)
}

fn main(b: bool) -> u8 {
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
        let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
        let mut eval: Evaluator = circuit.into();
        eval.set_bool(b);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, (b as u8) + 5);
    }
    Ok(())
}

#[test]
fn compile_exhaustive_enum_pattern_with_literals() -> Result<(), String> {
    let prg = "
enum Ops {
    Mul(u8, u8),
    Div(u8, u8),
}

fn main(choice: u8, x: u8, y: u8) -> u8 {
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
            let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
            let mut eval: Evaluator = circuit.into();
            eval.set_u8(choice);
            eval.set_u8(x);
            eval.set_u8(y);
            eval.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, expected);
        }
    }
    Ok(())
}

#[test]
fn compile_exhaustive_range_pattern() -> Result<(), String> {
    let prg = "
fn main(x: u8) -> u8 {
    match x {
        0..10 => 1,
        10 => 2,
        11 => 2,
        13 => 2,
        12..100 => 2,
        100..256 => 3,
    }
}
";
    for x in 0..255 {
        let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
        let mut eval: Evaluator = circuit.into();
        eval.set_u8(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        let expected = if x <= 9 {
            1
        } else if x <= 99 {
            2
        } else {
            3
        };
        assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, expected);
    }
    Ok(())
}

#[test]
fn compile_exhaustive_tuple_pattern() -> Result<(), String> {
    let prg = "
fn main(x: u8) -> u8 {
    let x = (false, x, -5);
    match x {
        (true, x, y) => 1,
        (false, 0, y) => 2,
        (false, x, y) => x,
    }
}
";
    for x in 0..10 {
        let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
        let mut eval: Evaluator = circuit.into();
        eval.set_u8(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        let expected = if x == 0 { 2 } else { x };
        assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, expected);
    }
    Ok(())
}

#[test]
fn compile_exhaustive_nested_pattern() -> Result<(), String> {
    let prg = "
fn main(x: u8) -> u8 {
    let x = (x, (x * 2, 1));
    match x {
        (0, _) => 1,
        (1..256, (x_twice, 1)) => x_twice,
        (1..256, (_, 1..256)) => 2,
        (1..256, (_, 0)) => 3,
    }
}
";
    for x in 0..10 {
        let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
        let mut eval: Evaluator = circuit.into();
        eval.set_u8(x);
        eval.run().map_err(|e| e.prettify(prg))?;
        let expected = if x == 0 { 1 } else { x * 2 };
        assert_eq!(eval.get_u8().map_err(|e| e.prettify(prg))?, expected);
    }
    Ok(())
}

#[test]
fn compile_main_with_tuple_io() -> Result<(), String> {
    let prg = "
fn main(values: (u8, u8)) -> (u8, u8) {
    (values.0 + 1, values.1 + 1)
}
";
    let checked = check(prg).map_err(|e| e.prettify(prg))?;
    let circuit = checked.compile();

    let mut eval: Evaluator = circuit.into();
    let tuple_ty = Type::Tuple(vec![Type::U8, Type::U8]);
    let input = Literal::parse(&checked, &tuple_ty, "(2, 3)").map_err(|e| e.prettify(""))?;
    eval.set_literal(&checked, input);
    eval.run().map_err(|e| e.prettify(prg))?;
    let r = eval
        .get_literal(&checked, &tuple_ty)
        .map_err(|e| e.prettify(prg))?;
    let expected = Literal::parse(&checked, &tuple_ty, "(3, 4)").map_err(|e| e.prettify(""))?;
    assert_eq!(r, expected);
    Ok(())
}

#[test]
fn compile_main_with_enum_io() -> Result<(), String> {
    let prg = "
enum Op {
    Zero,
    Div(u8, u8),
}

enum OpResult {
    DivByZero,
    Ok(u8),
}

fn main(op: Op) -> OpResult {
    match op {
        Op::Zero => OpResult::Ok(0),
        Op::Div(x, 0) => OpResult::DivByZero,
        Op::Div(x, y) => OpResult::Ok(x / y),
    }
}
";
    let checked = check(prg).map_err(|e| e.prettify(prg))?;
    let circuit = checked.compile();

    let mut eval: Evaluator = circuit.into();
    let ty_in = Type::Enum("Op".to_string());
    let ty_out = Type::Enum("OpResult".to_string());
    let input = Literal::parse(&checked, &ty_in, "Op::Div(10, 2)").map_err(|e| e.prettify(""))?;
    eval.set_literal(&checked, input);
    eval.run().map_err(|e| e.prettify(prg))?;
    let r = eval
        .get_literal(&checked, &ty_out)
        .map_err(|e| e.prettify(prg))?;
    let expected =
        Literal::parse(&checked, &ty_out, "OpResult::Ok(5)").map_err(|e| e.prettify(""))?;
    assert_eq!(r, expected);
    Ok(())
}

#[test]
fn compile_array_literal_access() -> Result<(), String> {
    let prg = "
fn main(i: usize) -> i8 {
    [-2, -1, 0 as i8, 1 as i8, 2 as i8][i]
}";
    let circuit = compile(prg).map_err(|e| e.prettify(prg))?;
    let mut eval: Evaluator = circuit.into();
    for i in 0..5 {
        eval.set_usize(i);
        eval.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(eval.get_i8().map_err(|e| e.prettify(prg))?, i as i8 - 2);
    }
    Ok(())
}

#[test]
fn compile_main_with_array_io() -> Result<(), String> {
    let prg = "
fn main(nums: [u8; 5]) -> [u8; 5] {
    let sum = nums.fold(0, |acc: u16, n: u8| -> u16 {
        acc + (n as u16)
    });
    nums.map(|n: u8| -> u8 {
        sum as u8
    })
}
";
    let checked = check(prg).map_err(|e| e.prettify(prg))?;
    let circuit = checked.compile();

    let mut eval: Evaluator = circuit.into();
    let array_ty = Type::Array(Box::new(Type::U8), 5);
    let input =
        Literal::parse(&checked, &array_ty, "[1, 2, 3, 4, 5]").map_err(|e| e.prettify(""))?;
    eval.set_literal(&checked, input);
    eval.run().map_err(|e| e.prettify(prg))?;
    let r = eval
        .get_literal(&checked, &array_ty)
        .map_err(|e| e.prettify(prg))?;
    let expected =
        Literal::parse(&checked, &array_ty, "[15, 15, 15, 15, 15]").map_err(|e| e.prettify(""))?;
    assert_eq!(r, expected);
    Ok(())
}
