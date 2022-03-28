use garble::{
    check::{TypeError, TypeErrorEnum},
    scan::scan,
    token::{MetaInfo, UnsignedNumType},
    typed_ast::{Pattern, PatternEnum, Program, Type},
    Error,
};

#[test]
fn reject_fns_as_values() -> Result<(), Error> {
    let prg = "
fn inc(x: u16) -> u16 {
  x + 1
}

pub fn main(x: u16) -> u16 {
  let f = inc;
  f(x)
}
";
    let e = scan(prg)?.parse()?.type_check();
    assert!(e.is_err());
    assert!(e
        .unwrap_err()
        .iter()
        .any(|TypeError(e, _)| matches!(e, TypeErrorEnum::UnknownIdentifier(_))));
    Ok(())
}

#[test]
fn reject_duplicate_fn_params() -> Result<(), Error> {
    let prg = "
fn add(x: u16, x: u16) -> u16 {
  x + x
}

pub fn main(x: u16) -> u16 {
  add(x, 1)
}
";
    let e = scan(prg)?.parse()?.type_check();
    let e = assert_single_type_error(e);
    assert!(matches!(e, TypeErrorEnum::DuplicateFnParam(_)));
    Ok(())
}

#[test]
fn reject_duplicate_fn_params_in_main() -> Result<(), Error> {
    let prg = "
pub fn main(x: u16, x: u16) -> u16 {
  x + x
}
";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    let e = assert_single_type_error(e);
    assert!(matches!(e, TypeErrorEnum::DuplicateFnParam(_)));
    Ok(())
}

#[test]
fn reject_unused_fn() -> Result<(), Error> {
    let prg = "
  pub fn main(x: u8) -> u8 {
    x
  }

  fn unused(x: u8) -> u8 {
    x + 1
  }
  ";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    let e = assert_single_type_error(e);
    assert!(matches!(e, TypeErrorEnum::UnusedFn(_)));
    Ok(())
}

#[test]
fn reject_recursive_fn() -> Result<(), Error> {
    let prg = "
  pub fn main(x: u8) -> u8 {
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
    let e = assert_single_type_error(e);
    assert!(matches!(e, TypeErrorEnum::RecursiveFnDef(_)));
    Ok(())
}

#[test]
fn reject_main_without_params() -> Result<(), Error> {
    let prg = "
pub fn main() -> u8 {
  0
}
";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    let e = assert_single_type_error(e);
    assert!(matches!(e, TypeErrorEnum::PubFnWithoutParams(_)));
    Ok(())
}

#[test]
fn reject_non_exhaustive_range_pattern() -> Result<(), Error> {
    let prg = "
pub fn main(x: u8) -> i32 {
  match x {
    0 => 0,
    1 => 1,
    3..10 => 2,
    11..255 => 3,
    256 => 4,
  }
}
  ";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    let e = assert_single_type_error(e);
    if let TypeErrorEnum::PatternsAreNotExhaustive(missing) = e {
        let meta = MetaInfo {
            start: (0, 0),
            end: (0, 0),
        };
        assert_eq!(
            missing,
            vec![
                [Pattern(
                    PatternEnum::UnsignedInclusiveRange(2, 2),
                    Type::Unsigned(UnsignedNumType::U8),
                    meta
                )],
                [Pattern(
                    PatternEnum::UnsignedInclusiveRange(10, 10),
                    Type::Unsigned(UnsignedNumType::U8),
                    meta
                )],
                [Pattern(
                    PatternEnum::UnsignedInclusiveRange(255, 255),
                    Type::Unsigned(UnsignedNumType::U8),
                    meta
                )]
            ]
        );
    } else {
        panic!("Expected patterns to be non-exhaustive, but found {e:?}");
    }
    Ok(())
}

#[test]
fn reject_non_exhaustive_tuple_pattern() -> Result<(), Error> {
    let prg = "
pub fn main(x: bool, y: bool, z: bool) -> i32 {
  match (x, (y, z)) {
    (true, _) => 1,
    (_, (false, true)) => 2,
    (false, (_, true)) => 3,
  }
}
  ";
    let e = scan(prg).unwrap().parse().unwrap().type_check();
    let e = assert_single_type_error(e);
    if let TypeErrorEnum::PatternsAreNotExhaustive(missing) = e {
        let meta = MetaInfo {
            start: (0, 0),
            end: (0, 0),
        };
        assert_eq!(
            missing,
            vec![
                [Pattern(
                    PatternEnum::Tuple(vec![
                        Pattern(PatternEnum::False, Type::Bool, meta),
                        Pattern(
                            PatternEnum::Tuple(vec![
                                Pattern(PatternEnum::True, Type::Bool, meta),
                                Pattern(PatternEnum::False, Type::Bool, meta),
                            ]),
                            Type::Tuple(vec![Type::Bool, Type::Bool]),
                            meta
                        ),
                    ]),
                    Type::Tuple(vec![Type::Bool, Type::Tuple(vec![Type::Bool, Type::Bool])]),
                    meta
                )],
                [Pattern(
                    PatternEnum::Tuple(vec![
                        Pattern(PatternEnum::False, Type::Bool, meta),
                        Pattern(
                            PatternEnum::Tuple(vec![
                                Pattern(PatternEnum::False, Type::Bool, meta),
                                Pattern(PatternEnum::False, Type::Bool, meta),
                            ]),
                            Type::Tuple(vec![Type::Bool, Type::Bool]),
                            meta
                        ),
                    ]),
                    Type::Tuple(vec![Type::Bool, Type::Tuple(vec![Type::Bool, Type::Bool])]),
                    meta
                )],
            ]
        );
    } else {
        panic!("Expected patterns to be non-exhaustive, but found {e:?}");
    }
    Ok(())
}

#[test]
fn reject_access_outside_lexical_scope() -> Result<(), Error> {
    let prg = "
pub fn main(x: i32) -> i32 {
  let y = {
    let z = 1;
    z
  };
  z
}
";
    let e = scan(prg)?.parse()?.type_check();
    let e = assert_single_type_error(e);
    assert!(matches!(e, TypeErrorEnum::UnknownIdentifier(_)));
    Ok(())
}

fn assert_single_type_error(e: Result<Program, Vec<TypeError>>) -> TypeErrorEnum {
    if let Err(mut e) = e {
        if e.len() == 1 {
            return e.pop().unwrap().0;
        } else {
            panic!("Expected a single type error, but found {e:?}");
        }
    } else {
        panic!("Expected an error, but found {e:?}");
    }
}
