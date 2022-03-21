use std::{fs::File, io::Read};

use garble::{
    check, compile,
    eval::Evaluator,
    literal::{Literal, VariantLiteral},
    token::UnsignedNumType,
    Error,
};

#[test]
fn smart_cookie_simple_interaction() -> Result<(), Error> {
    let init = read_source_code("init.garble.rs");
    let log_interest = read_source_code("log_interest.garble.rs");
    let decide_ad = read_source_code("decide_ad.garble.rs");

    let init_checked = check(&init).map_err(|e| pretty_print(e, &init))?;
    let log_interest_checked = check(&log_interest).map_err(|e| pretty_print(e, &log_interest))?;
    let decide_ad_checked = check(&decide_ad).map_err(|e| pretty_print(e, &decide_ad))?;

    let init_circuit = compile(&init)?;
    let log_interest_circuit = compile(&log_interest)?;
    let decide_ad_circuit = compile(&decide_ad)?;

    let website_signing_key = Literal::NumUnsigned(0, UnsignedNumType::U128);

    let mut init_eval = Evaluator::from(&init_circuit);
    init_eval
        .parse_literal(&init_checked, "()")
        .map_err(|e| pretty_print(e, &init))?;
    init_eval
        .set_literal(&init_checked, website_signing_key.clone())
        .map_err(|e| pretty_print(e, &init))?;
    let mut user_state = init_eval
        .run()
        .map_err(|e| pretty_print(e, &init))?
        .into_literal(&init_checked)
        .map_err(|e| pretty_print(e, &init))?;

    for interest in ["Politics", "Politics", "Cars", "Luxury", "Cars", "Cars"] {
        let mut log_interest_eval = Evaluator::from(&log_interest_circuit);
        log_interest_eval
            .set_literal(&log_interest_checked, user_state)
            .map_err(|e| pretty_print(e, &log_interest))?;
        let interest = Literal::Enum(
            "UserInterest".to_string(),
            interest.to_string(),
            VariantLiteral::Unit,
        );
        log_interest_eval
            .set_literal(
                &log_interest_checked,
                Literal::Tuple(vec![interest, website_signing_key.clone()]),
            )
            .map_err(|e| pretty_print(e, &log_interest))?;
        let log_interest_result = log_interest_eval
            .run()
            .map_err(|e| pretty_print(e, &log_interest))?
            .into_literal(&log_interest_checked)
            .map_err(|e| pretty_print(e, &log_interest))?;
        user_state = Literal::Tuple(expect_enum(
            &log_interest_result,
            "LogInterestResult",
            "Ok",
            Some(2),
        ));
    }

    let mut decide_ad_eval = Evaluator::from(&decide_ad_circuit);
    decide_ad_eval
        .set_literal(&decide_ad_checked, user_state)
        .map_err(|e| pretty_print(e, &decide_ad))?;
    decide_ad_eval
        .set_literal(&decide_ad_checked, website_signing_key)
        .map_err(|e| pretty_print(e, &decide_ad))?;
    let ad_decision = decide_ad_eval
        .run()
        .map_err(|e| pretty_print(e, &decide_ad))?
        .into_literal(&decide_ad_checked)
        .map_err(|e| pretty_print(e, &decide_ad))?;

    let ad_decision = expect_enum(&ad_decision, "AdDecisionResult", "Ok", Some(1));
    assert_eq!(
        ad_decision[0],
        Literal::Enum(
            "UserInterest".to_string(),
            "Cars".to_string(),
            VariantLiteral::Unit
        )
    );
    Ok(())
}

#[test]
fn smart_cookie_larger_than_buffer_interaction() -> Result<(), Error> {
    let init = read_source_code("init.garble.rs");
    let log_interest = read_source_code("log_interest.garble.rs");
    let decide_ad = read_source_code("decide_ad.garble.rs");

    let init_checked = check(&init).map_err(|e| pretty_print(e, &init))?;
    let log_interest_checked = check(&log_interest).map_err(|e| pretty_print(e, &log_interest))?;
    let decide_ad_checked = check(&decide_ad).map_err(|e| pretty_print(e, &decide_ad))?;

    let init_circuit = compile(&init)?;
    let log_interest_circuit = compile(&log_interest)?;
    let decide_ad_circuit = compile(&decide_ad)?;

    let website_signing_key = Literal::NumUnsigned(0, UnsignedNumType::U128);

    let mut init_eval = Evaluator::from(&init_circuit);
    init_eval
        .parse_literal(&init_checked, "()")
        .map_err(|e| pretty_print(e, &init))?;
    init_eval
        .set_literal(&init_checked, website_signing_key.clone())
        .map_err(|e| pretty_print(e, &init))?;
    let mut user_state = init_eval
        .run()
        .map_err(|e| pretty_print(e, &init))?
        .into_literal(&init_checked)
        .map_err(|e| pretty_print(e, &init))?;

    for interest in ["Politics"; 20].iter().chain(["Luxury"; 500].iter()) {
        let mut log_interest_eval = Evaluator::from(&log_interest_circuit);
        log_interest_eval
            .set_literal(&log_interest_checked, user_state)
            .map_err(|e| pretty_print(e, &log_interest))?;
        let interest = Literal::Enum(
            "UserInterest".to_string(),
            interest.to_string(),
            VariantLiteral::Unit,
        );
        log_interest_eval
            .set_literal(
                &log_interest_checked,
                Literal::Tuple(vec![interest, website_signing_key.clone()]),
            )
            .map_err(|e| pretty_print(e, &log_interest))?;
        let log_interest_result = log_interest_eval
            .run()
            .map_err(|e| pretty_print(e, &log_interest))?
            .into_literal(&log_interest_checked)
            .map_err(|e| pretty_print(e, &log_interest))?;
        user_state = Literal::Tuple(expect_enum(
            &log_interest_result,
            "LogInterestResult",
            "Ok",
            Some(2),
        ));
    }

    let mut decide_ad_eval = Evaluator::from(&decide_ad_circuit);
    decide_ad_eval
        .set_literal(&decide_ad_checked, user_state)
        .map_err(|e| pretty_print(e, &decide_ad))?;
    decide_ad_eval
        .set_literal(&decide_ad_checked, website_signing_key)
        .map_err(|e| pretty_print(e, &decide_ad))?;
    let ad_decision = decide_ad_eval
        .run()
        .map_err(|e| pretty_print(e, &decide_ad))?
        .into_literal(&decide_ad_checked)
        .map_err(|e| pretty_print(e, &decide_ad))?;

    let ad_decision = expect_enum(&ad_decision, "AdDecisionResult", "Ok", Some(1));
    assert_eq!(
        ad_decision[0],
        Literal::Enum(
            "UserInterest".to_string(),
            "Luxury".to_string(),
            VariantLiteral::Unit
        )
    );
    Ok(())
}

fn expect_enum(
    l: &Literal,
    enum_name: &str,
    variant_name: &str,
    fields: Option<usize>,
) -> Vec<Literal> {
    match &l {
        Literal::Enum(actual_enum_name, actual_variant_name, actual_fields) => {
            if actual_enum_name.as_str() == enum_name
                && actual_variant_name.as_str() == variant_name
            {
                match actual_fields {
                    VariantLiteral::Tuple(actual_fields)
                        if fields.is_some() && fields.unwrap() == actual_fields.len() =>
                    {
                        actual_fields.clone()
                    }
                    VariantLiteral::Unit if fields.is_none() => vec![],
                    _ => {
                        panic!("Expected a variant with {fields:?} fields, found {actual_fields:?}")
                    }
                }
            } else {
                panic!("Unexpected enum: {l}");
            }
        }
        _ => panic!("Unexpected ad decision result: {l}"),
    }
}

fn read_source_code(file_name: &str) -> String {
    let path = format!("./garble_examples/smart_cookie/{file_name}");
    let mut source_file = File::open(&path).unwrap_or_else(|_| panic!("Could not open {path}"));
    let mut source_code = String::new();
    source_file
        .read_to_string(&mut source_code)
        .unwrap_or_else(|_| panic!("Could not read {path}"));
    source_code
}

fn pretty_print<E: Into<Error>>(e: E, prg: &str) -> Error {
    let e: Error = e.into();
    let pretty = e.prettify(prg);
    println!("{}", pretty);
    e
}
