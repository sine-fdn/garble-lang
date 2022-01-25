use garble_script::{ast::Party, compile, compiler::Computation, Error};

#[test]
fn compile_xor() -> Result<(), Error> {
    for y in [true, false] {
        let prg = format!("(fn main bool (param x A bool) (^ x {}))", y);
        let circuit = compile(&prg)?;
        let mut computation: Computation = circuit.into();
        for x in [true, false] {
            computation.set_bool(Party::A, x);
            computation.run()?;
            assert_eq!(computation.get_bool()?, x ^ y);
        }
    }
    Ok(())
}

#[test]
fn compile_add() -> Result<(), Error> {
    for y in 0..127 {
        let prg = format!("(fn main u8 (param x A u8) (+ x {}))", y);
        let circuit = compile(&prg)?;
        let mut computation: Computation = circuit.into();
        for x in 0..127 {
            computation.set_u8(Party::A, x);
            computation.run()?;
            assert_eq!(computation.get_u8()?, x + y);
        }
    }
    Ok(())
}

#[test]
fn compile_add_with_int_coercion() -> Result<(), Error> {
    for y in 240..280 {
        let prg = format!("(fn main u16 (param x A u16) (+ x {}))", y);
        let circuit = compile(&prg)?;
        let mut computation: Computation = circuit.into();
        for x in 240..280 {
            computation.set_u16(Party::A, x);
            computation.run()?;
            assert_eq!(computation.get_u16()?, x + y);
        }
    }
    Ok(())
}

#[test]
fn compile_let_expr() -> Result<(), String> {
    let prg = "
(fn main u16 (param x A u16)
  (let y (+ x 1)
    (+ y 1)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    computation.set_u16(Party::A, 255);
    computation.run().map_err(|e| e.prettify(prg))?;
    assert_eq!(computation.get_u16().map_err(|e| e.prettify(prg))?, 257);
    Ok(())
}

#[test]
fn compile_static_fn_defs() -> Result<(), String> {
    let prg = "
(fn add u16 (param x u16) (param y u16)
  (+ x y))

(fn inc u16 (param x u16)
  (call add x 1))

(fn main u16 (param x A u16)
  (call inc x))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    computation.set_u16(Party::A, 255);
    computation.run().map_err(|e| e.prettify(prg))?;
    assert_eq!(computation.get_u16().map_err(|e| e.prettify(prg))?, 256);
    Ok(())
}

#[test]
fn compile_if() -> Result<(), String> {
    let prg = "
(fn main u8 (param x A bool)
  (if (^ (& true false) x)
    100
    50))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for b in [true, false] {
        let expected = if b { 100 } else { 50 };
        computation.set_bool(Party::A, b);
        computation.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(computation.get_u8().map_err(|e| e.prettify(prg))?, expected);
    }
    Ok(())
}

#[test]
fn compile_bit_ops_for_numbers() -> Result<(), String> {
    let prg = "
(fn main u16 (param x A u16) (param y A u16) (param z A u16)
  (| x (& y (^ z 2))))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 10..20 {
        for y in 10..20 {
            for z in 10..20 {
                let expected = x | (y & (z ^ 2));
                computation.set_u16(Party::A, x);
                computation.set_u16(Party::A, y);
                computation.set_u16(Party::A, z);
                computation.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(
                    computation.get_u16().map_err(|e| e.prettify(prg))?,
                    expected
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_greater_than_and_less_than() -> Result<(), String> {
    let prg = "
(fn main bool (param x A u16) (param y A u16)
  (&
    (> x y)
    (< x 10)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 5..15 {
        for y in 5..15 {
            let expected = (x > y) && (x < 10);
            computation.set_u16(Party::A, x);
            computation.set_u16(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(
                computation.get_bool().map_err(|e| e.prettify(prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_equals_and_not_equals() -> Result<(), String> {
    let prg = "
(fn main bool (param x A u16) (param y A u16)
  (& (== x y) (!= x 0)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 0..2 {
        for y in 0..2 {
            let expected = (x == y) && (x != 0);
            computation.set_u16(Party::A, x);
            computation.set_u16(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(
                computation.get_bool().map_err(|e| e.prettify(prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_casts() -> Result<(), String> {
    let prg = "
(fn main u16 (param x A u16) (param y A u8)
  (+ (cast u16 (cast u8 x)) (cast u16 y)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 200..300 {
        for y in 0..10 {
            let expected = (x as u8) as u16 + (y as u16);
            computation.set_u16(Party::A, x);
            computation.set_u8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(
                computation.get_u16().map_err(|e| e.prettify(prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_bool_casts() -> Result<(), String> {
    let prg = "
(fn main u16 (param x A bool) (param y A u8)
  (+ (cast u16 x) (cast u16 y)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in [true, false] {
        for y in 0..10 {
            let expected = (x as u16) + (y as u16);
            computation.set_bool(Party::A, x);
            computation.set_u8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(
                computation.get_u16().map_err(|e| e.prettify(prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_bit_shifts() -> Result<(), String> {
    let prg = "
(fn main u16 (param mode A bool) (param x A u16) (param y A u8)
  (if mode
    (<< x y)
    (>> x y)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
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
                computation.set_bool(Party::A, mode);
                computation.set_u16(Party::A, x);
                computation.set_u8(Party::A, y);
                computation.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(
                    computation.get_u16().map_err(|e| e.prettify(prg))?,
                    expected
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_nums() -> Result<(), String> {
    let prg = "
(fn main i8 (param x A i8)
  x)
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -128..127 {
        computation.set_i8(Party::A, x);
        computation.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(computation.get_i8().map_err(|e| e.prettify(prg))?, x);
    }
    Ok(())
}

#[test]
fn compile_signed_add() -> Result<(), String> {
    let prg = "
(fn main i8 (param x A i8) (param y A i8)
  (+ x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -64..64 {
        for y in -64..63 {
            computation.set_i8(Party::A, x);
            computation.set_i8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i8().map_err(|e| e.prettify(prg))?, x + y);
        }
    }
    Ok(())
}

#[test]
fn compile_bit_ops_for_signed_numbers() -> Result<(), String> {
    let prg = "
(fn main i16 (param x A i16) (param y A i16) (param z A i16)
  (| x (& y (^ z 2))))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -10..10 {
        for y in -10..10 {
            for z in -10..10 {
                let expected = x | (y & (z ^ 2));
                computation.set_i16(Party::A, x);
                computation.set_i16(Party::A, y);
                computation.set_i16(Party::A, z);
                computation.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(
                    computation.get_i16().map_err(|e| e.prettify(prg))?,
                    expected
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_signed_greater_than_and_less_than() -> Result<(), String> {
    let prg = "
(fn main bool (param x A i16) (param y A i16)
  (&
    (> x y)
    (< y x)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -10..10 {
        for y in -10..10 {
            let expected = (x > y) && (y < x);
            computation.set_i16(Party::A, x);
            computation.set_i16(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(
                computation.get_bool().map_err(|e| e.prettify(prg))?,
                expected
            );
        }
    }
    Ok(())
}

#[test]
fn compile_signed_bit_shifts() -> Result<(), String> {
    let prg = "
(fn main i16 (param mode A bool) (param x A i16) (param y A u8)
  (if mode
    (<< x y)
    (>> x y)))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
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
                computation.set_bool(Party::A, mode);
                computation.set_i16(Party::A, x);
                computation.set_u8(Party::A, y);
                computation.run().map_err(|e| e.prettify(prg))?;
                assert_eq!(
                    computation.get_i16().map_err(|e| e.prettify(prg))?,
                    expected
                );
            }
        }
    }
    Ok(())
}

#[test]
fn compile_add_with_signed_int_coercion() -> Result<(), String> {
    let prg = "
(fn main i16 (param x A i16)
  (+ x -10))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -10..10 {
        let expected = x + -10;
        computation.set_i16(Party::A, x);
        computation.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(
            computation.get_i16().map_err(|e| e.prettify(prg))?,
            expected
        );
    }
    Ok(())
}

#[test]
fn compile_sub() -> Result<(), String> {
    let prg = "
(fn main i16 (param x A i16) (param y A i16)
  (- x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -10..20 {
        for y in -10..256 {
            computation.set_i16(Party::A, x);
            computation.set_i16(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i16().map_err(|e| e.prettify(prg))?, x - y);
        }
    }
    Ok(())
}

#[test]
fn compile_unary_negation() -> Result<(), String> {
    let prg = "
(fn main i16 (param x A i16)
  (- x))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -127..127 {
        computation.set_i16(Party::A, x);
        computation.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(computation.get_i16().map_err(|e| e.prettify(prg))?, -x);
    }
    Ok(())
}

#[test]
fn compile_unary_not() -> Result<(), String> {
    let prg = "
(fn main i16 (param x A i16)
  (! x))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -127..127 {
        computation.set_i16(Party::A, x);
        computation.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(computation.get_i16().map_err(|e| e.prettify(prg))?, !x);
    }

    let prg = "
(fn main bool (param x A bool)
  (! x))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for b in [true, false] {
        computation.set_bool(Party::A, b);
        computation.run().map_err(|e| e.prettify(prg))?;
        assert_eq!(computation.get_bool().map_err(|e| e.prettify(prg))?, !b);
    }
    Ok(())
}

#[test]
fn compile_unsigned_mul() -> Result<(), String> {
    let prg = "
(fn main u16 (param x A u16) (param y A u16)
  (* x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 0..20 {
        for y in 250..300 {
            computation.set_u16(Party::A, x);
            computation.set_u16(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_u16().map_err(|e| e.prettify(prg))?, x * y);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_mul() -> Result<(), String> {
    let prg = "
(fn main i16 (param x A i16) (param y A i16)
  (* x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -10..10 {
        for y in -10..10 {
            computation.set_i16(Party::A, x);
            computation.set_i16(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i16().map_err(|e| e.prettify(prg))?, x * y);
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_div() -> Result<(), String> {
    let prg = "
(fn main u8 (param x A u8) (param y A u8)
  (/ x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 0..255 {
        for y in 1..10 {
            computation.set_u8(Party::A, x);
            computation.set_u8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_u8().map_err(|e| e.prettify(prg))?, x / y);
        }
        for y in 250..255 {
            computation.set_u8(Party::A, x);
            computation.set_u8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_u8().map_err(|e| e.prettify(prg))?, x / y);
        }
    }
    Ok(())
}

#[test]
fn compile_unsigned_mod() -> Result<(), String> {
    let prg = "
(fn main u8 (param x A u8) (param y A u8)
  (% x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in 0..255 {
        for y in 1..10 {
            computation.set_u8(Party::A, x);
            computation.set_u8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_u8().map_err(|e| e.prettify(prg))?, x % y);
        }
        for y in 250..255 {
            computation.set_u8(Party::A, x);
            computation.set_u8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_u8().map_err(|e| e.prettify(prg))?, x % y);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_div() -> Result<(), String> {
    let prg = "
(fn main i8 (param x A i8) (param y A i8)
  (/ x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -128..127 {
        for y in -4..5 {
            if y == -1 || y == 0 {
                continue;
            }
            computation.set_i8(Party::A, x);
            computation.set_i8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i8().map_err(|e| e.prettify(prg))?, x / y);
        }
        for y in 120..127 {
            computation.set_i8(Party::A, x);
            computation.set_i8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i8().map_err(|e| e.prettify(prg))?, x / y);
        }
    }
    Ok(())
}

#[test]
fn compile_signed_mod() -> Result<(), String> {
    let prg = "
(fn main i8 (param x A i8) (param y A i8)
  (% x y))
";
    let circuit = compile(&prg).map_err(|e| e.prettify(prg))?;
    let mut computation: Computation = circuit.into();
    for x in -128..127 {
        for y in -4..5 {
            if y == -1 || y == 0 {
                continue;
            }
            computation.set_i8(Party::A, x);
            computation.set_i8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i8().map_err(|e| e.prettify(prg))?, x % y);
        }
        for y in 120..127 {
            computation.set_i8(Party::A, x);
            computation.set_i8(Party::A, y);
            computation.run().map_err(|e| e.prettify(prg))?;
            assert_eq!(computation.get_i8().map_err(|e| e.prettify(prg))?, x % y);
        }
    }
    Ok(())
}
