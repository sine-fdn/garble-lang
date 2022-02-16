use garble_script::{
    check::{TypeError, TypeErrorEnum},
    scan::scan,
    Error,
};

#[test]
fn reject_fns_as_values() -> Result<(), Error> {
    let prg = "
fn inc(x: u16) -> u16 {
  x + 1
}

fn main(x: u16) -> u16 {
  let f = inc;
  f(x)
}
";
    let e = scan(prg)?.parse()?.type_check();
    assert!(matches!(
        e,
        Err(TypeError(TypeErrorEnum::UnknownIdentifier(_), _))
    ));
    Ok(())
}

#[test]
fn reject_duplicate_fn_params() -> Result<(), Error> {
    let prg = "
fn add(x: u16, x: u16) -> u16 {
  x + x
}

fn main(x: u16) -> u16 {
  add(x, 1)
}
";
    let e = scan(prg)?.parse()?.type_check();
    assert!(matches!(
        e,
        Err(TypeError(TypeErrorEnum::DuplicateFnParam(_), _))
    ));
    Ok(())
}

#[test]
fn reject_duplicate_fn_params_in_main() -> Result<(), Error> {
    let prg = "
fn main(x: u16, x: u16) -> u16 {
  x + x
}
";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    assert!(matches!(
        e,
        Err(TypeError(TypeErrorEnum::DuplicateFnParam(_), _))
    ));
    Ok(())
}

#[test]
fn reject_unused_fn() -> Result<(), Error> {
    let prg = "
  fn main(x: u8) -> u8 {
    x
  }

  fn unused(x: u8) -> u8 {
    x + 1
  }
  ";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    assert!(matches!(e, Err(TypeError(TypeErrorEnum::UnusedFn(_), _))));
    Ok(())
}

#[test]
fn reject_recursive_fn() -> Result<(), Error> {
    let prg = "
  fn main(x: u8) -> u8 {
    rec_fn(x)
  }

  fn rec_fn(x: u8) -> u8 {
    if x == 0 {
      0
    } else {
      rec_fn(x - 1)
    }
  }
  ";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    assert!(matches!(
        e,
        Err(TypeError(TypeErrorEnum::RecursiveFnDef(_), _))
    ));
    Ok(())
}

#[test]
fn reject_main_without_params() -> Result<(), Error> {
    let prg = "
fn main() -> u8 {
  0
}
";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    assert!(matches!(
        e,
        Err(TypeError(TypeErrorEnum::NoMainFnParams, _))
    ));
    Ok(())
}
