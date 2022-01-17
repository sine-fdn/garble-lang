use garble_script::{ast::Party, compile, compiler::Computation, Error};

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
