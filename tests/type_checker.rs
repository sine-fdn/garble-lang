use garble_script::{parser::parse, type_checker::{TypeError, TypeErrorEnum}};

#[test]
fn reject_fns_as_values() -> Result<(), String> {
    let prg = "
(fn inc u16 (param x u16)
  (+ x 1))

(fn main u16 (param x A u16)
  (let f inc
    (call f x)))
";
    let e = parse(prg)
        .map_err(|e| e.prettify(prg))?
        .type_check();
    assert!(matches!(e, Err(TypeError(TypeErrorEnum::FnCannotBeUsedAsValue(_), _))));
    Ok(())
}

#[test]
fn reject_duplicate_fn_params() -> Result<(), String> {
    let prg = "
(fn add u16 (param x u16) (param x u16)
  (+ x x))

(fn main u16 (param x A u16)
  (call add x 1))
";
    let e = parse(prg)
        .map_err(|e| e.prettify(prg))?
        .type_check();
    assert!(matches!(e, Err(TypeError(TypeErrorEnum::DuplicateFnParam(_), _))));
    Ok(())
}

#[test]
fn reject_duplicate_fn_params_in_main() -> Result<(), String> {
    let prg = "
(fn main u16 (param x A u16) (param x A u16)
  (+ x x))
";
    let e = parse(prg)
        .map_err(|e| e.prettify(prg))?
        .type_check();
    assert!(matches!(e, Err(TypeError(TypeErrorEnum::DuplicateFnParam(_), _))));
    Ok(())
}
