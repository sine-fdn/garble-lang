use garble_lang::{compile, compile_with_constants, literal::Literal, token::UnsignedNumType};

#[test]
fn parse_custom_join() -> Result<(), ()> {
    let source = "
const ROWS_0: usize = PARTY_0::DB_SIZE;
const ROWS_1: usize = PARTY_1::DB_SIZE;

pub fn main(rows0: [(u32); ROWS_0], rows1: [(u32); ROWS_1]) -> [(bool, ((u32), (u32))); const { ROWS_0 + ROWS_1 - 1}] {
    custom_join(rows0, rows1)
}
";
    let consts = [
        (
            "PARTY_0".into(),
            [(
                "DB_SIZE".into(),
                Literal::NumUnsigned(1, UnsignedNumType::Usize),
            )]
            .into_iter()
            .collect(),
        ),
        (
            "PARTY_1".into(),
            [(
                "DB_SIZE".into(),
                Literal::NumUnsigned(2, UnsignedNumType::Usize),
            )]
            .into_iter()
            .collect(),
        ),
    ]
    .into_iter()
    .collect();

    let prg =
        compile_with_constants(source, consts).map_err(|e| eprintln!("{}", e.prettify(source)))?;

    let mut eval = prg.evaluator();

    eval.set_literal(Literal::Array(vec![
        // Literal::Tuple(vec![Literal::NumUnsigned(0, UnsignedNumType::U32)]),
        Literal::Tuple(vec![Literal::NumUnsigned(1, UnsignedNumType::U32)]),
    ]))
    .expect("Setting input for P0");

    eval.set_literal(Literal::Array(vec![
        Literal::Tuple(vec![Literal::NumUnsigned(1, UnsignedNumType::U32)]),
        Literal::Tuple(vec![Literal::NumUnsigned(3, UnsignedNumType::U32)]),
    ]))
    .expect("Setting input for P1");

    let out = eval.run().expect("running eval");
    let lit = out.into_literal().expect("output decoding");
    dbg!(lit);

    Ok(())
}
