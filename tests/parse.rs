use garble_lang::{
    parse::{ParseError, ParseErrorEnum},
    scan::scan,
    Error, UntypedProgram,
};

#[test]
// TODO we might want to allow this in the future (robinhundt 31.07.25)
fn reject_array_repeat_const_expr_size() -> Result<(), Error> {
    let prg = "
pub fn main(b: u8) -> u8 {
  let a = [4; const { 2 + 3 } ];
  b
}
";
    let e = scan(prg)?.parse();
    let e = assert_single_parse_error(e);
    assert!(matches!(e, ParseErrorEnum::InvalidArraySize));
    Ok(())
}

fn assert_single_parse_error(e: Result<UntypedProgram, Vec<ParseError>>) -> ParseErrorEnum {
    if let Err(mut e) = e {
        if e.len() == 1 {
            e.pop().unwrap().0
        } else {
            panic!("Expected a single parse error, but found {e:?}");
        }
    } else {
        panic!("Expected an error, but found {e:?}");
    }
}
