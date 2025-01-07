#![cfg(feature = "serde")]
use garble_lang::{
    literal::{Literal, VariantLiteral},
    token::{SignedNumType, UnsignedNumType},
};

#[test]
fn serde_true() -> Result<(), String> {
    let literal = Literal::True;
    let expected = "\"True\"";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}

#[test]
fn serde_int_unsigned() -> Result<(), String> {
    let literal = Literal::NumUnsigned(200, UnsignedNumType::U32);
    let expected = "{\"NumUnsigned\":[200,\"U32\"]}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}

#[test]
fn serde_int_signed() -> Result<(), String> {
    let literal = Literal::NumSigned(-200, SignedNumType::Unspecified);
    let expected = "{\"NumSigned\":[-200,\"Unspecified\"]}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}

#[test]
fn serde_array_repeat() -> Result<(), String> {
    let literal = Literal::ArrayRepeat(Box::new(Literal::True), 3);
    let expected = "{\"ArrayRepeat\":[\"True\",3]}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}

#[test]
fn serde_array() -> Result<(), String> {
    let literal = Literal::Array(vec![Literal::True, Literal::False]);
    let expected = "{\"Array\":[\"True\",\"False\"]}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
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
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}

#[test]
fn serde_struct() -> Result<(), String> {
    let literal = Literal::Struct(
        "FooBar".to_string(),
        vec![
            ("Foo".to_string(), Literal::True),
            ("Bar".to_string(), Literal::False),
        ],
    );
    let expected = "{\"Struct\":[\"FooBar\",[[\"Foo\",\"True\"],[\"Bar\",\"False\"]]]}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
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
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
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
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}

#[test]
fn serde_range() -> Result<(), String> {
    let literal = Literal::Range(2, 10, UnsignedNumType::U8);
    let expected = "{\"Range\":[2,10,\"U8\"]}";
    let json = serde_json::to_string(&literal).unwrap();
    assert_eq!(json, expected);
    assert_eq!(literal, serde_json::from_str::<Literal>(&json).unwrap());
    Ok(())
}
