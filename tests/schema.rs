#![cfg(feature = "json_schema")]
use garble_lang::literal::Literal;
use insta::assert_json_snapshot;
use schemars::schema_for;

/// This is a snapshot test using [insta](https://docs.rs/insta/latest/insta/)
/// for the json schema of the `Literal` type. If the test fails, you'll need
/// to update the stored snapshot in the `./snapshots` folder. You can update
/// the snapshots using the `cargo-insta` tool or using the `INSTA_UPDATE` env
/// variable (see here https://docs.rs/insta/latest/insta/#writing-tests).
#[test]
fn print_literal_schema() {
    let schema = schema_for!(Literal);
    assert_json_snapshot!(schema, {
        // We ignore all descriptions so that changing them doesn't cause
        // the test to fail.
        ".**.description" => ""
    });
}
