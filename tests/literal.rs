#![cfg(feature = "serde")]
use garble_lang::{
    literal::{Literal, VariantLiteral},
    token::{SignedNumType, UnsignedNumType},
};

#[test]
fn serde_true() -> Result<(), String> {
    let literal = Literal::True;
    let expected = "\"True\"";
    let as_garble_code = "true";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_int_unsigned() -> Result<(), String> {
    let literal = Literal::NumUnsigned(200, UnsignedNumType::U32);
    let expected = "{\"NumUnsigned\":[200,\"U32\"]}";
    let as_garble_code = "200";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_int_signed() -> Result<(), String> {
    let literal = Literal::NumSigned(-200, SignedNumType::Unspecified);
    let expected = "{\"NumSigned\":[-200,\"Unspecified\"]}";
    let as_garble_code = "-200";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_array_repeat() -> Result<(), String> {
    let literal = Literal::ArrayRepeat(Box::new(Literal::True), 3);
    let expected = "{\"ArrayRepeat\":[\"True\",3]}";
    let as_garble_code = "[true; 3]";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_array() -> Result<(), String> {
    let literal = Literal::Array(vec![Literal::True, Literal::False]);
    let expected = "{\"Array\":[\"True\",\"False\"]}";
    let as_garble_code = "[true, false]";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_tuple() -> Result<(), String> {
    let literal = Literal::Tuple(vec![
        Literal::True,
        Literal::False,
        Literal::NumUnsigned(10, UnsignedNumType::U8),
    ]);
    let expected = "{\"Tuple\":[\"True\",\"False\",{\"NumUnsigned\":[10,\"U8\"]}]}";
    let as_garble_code = "(true, false, 10)";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_struct() -> Result<(), String> {
    let literal = Literal::Struct(
        "FooBar".to_string(),
        vec![
            ("foo".to_string(), Literal::True),
            ("bar".to_string(), Literal::False),
        ],
    );
    let expected = "{\"Struct\":[\"FooBar\",[[\"foo\",\"True\"],[\"bar\",\"False\"]]]}";
    let as_garble_code = "FooBar {foo: true, bar: false}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_enum_unit() -> Result<(), String> {
    let literal = Literal::Enum(
        "FooBar".to_string(),
        "Foo".to_string(),
        VariantLiteral::Unit,
    );
    let expected = "{\"Enum\":[\"FooBar\",\"Foo\",\"Unit\"]}";
    let as_garble_code = "FooBar::Foo";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_enum_tuple() -> Result<(), String> {
    let literal = Literal::Enum(
        "FooBar".to_string(),
        "Bar".to_string(),
        VariantLiteral::Tuple(vec![Literal::True, Literal::False]),
    );
    let expected = "{\"Enum\":[\"FooBar\",\"Bar\",{\"Tuple\":[\"True\",\"False\"]}]}";
    let as_garble_code = "FooBar::Bar(true, false)";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}

#[test]
fn serde_range() -> Result<(), String> {
    let literal = Literal::Range(2, 10, UnsignedNumType::U8);
    let expected = "{\"Range\":[2,10,\"U8\"]}";
    let as_garble_code = "2u8..10u8";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    assert_eq!(literal.to_string(), as_garble_code);
    Ok(())
}
