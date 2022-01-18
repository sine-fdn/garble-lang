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
