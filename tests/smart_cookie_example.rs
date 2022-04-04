#![cfg(feature = "smart-cookie")]

use std::{fs::File, io::Read};

use garble::{
    check,
    eval::Evaluator,
    literal::{Literal, VariantLiteral},
    token::UnsignedNumType,
    Error,
};

#[test]
fn smart_cookie_simple_interaction() -> Result<(), Error> {
    let interests1 = (
        "Cars",
        vec!["Politics", "Politics", "Cars", "Luxury", "Cars", "Cars"],
    );
    let interests2 = (
        "Luxury",
        ["Politics"; 20]
            .into_iter()
            .chain(["Luxury"; 40].into_iter())
            .collect::<Vec<_>>(),
    );

    for (expected_ad_decision, interests) in [interests1, interests2] {
        let smart_cookie = read_source_code("smart_cookie.garble.rs");
        println!("Parsing and type-checking...");
        let program = check(&smart_cookie).map_err(|e| pretty_print(e, &smart_cookie))?;
        println!("Compiling...");

        let (init_circuit, init_fn) = program.compile("init")?;
        println!(">> 'init' has {}", init_circuit.report_gates());

        let (log_interest_circuit, log_interest_fn) = program.compile("log_interest")?;
        println!(
            ">> 'log_interest' has {}",
            log_interest_circuit.report_gates()
        );

        let (decide_ad_circuit, decide_ad_fn) = program.compile("decide_ad")?;
        println!(">> 'decide_ad' has {}", decide_ad_circuit.report_gates());

        let key: [u8; 16] = [7, 3, 4, 3, 2, 7, 3, 4, 9, 0, 2, 0, 0, 4, 2, 8];

        let website_signing_key = Literal::Struct(
            "SigningKey".to_string(),
            vec![(
                "key".to_string(),
                Literal::Array(
                    key.iter()
                        .map(|byte| Literal::NumUnsigned(*byte as u128, UnsignedNumType::U8))
                        .collect(),
                ),
            )],
        );

        let mut init_eval = Evaluator::new(&program, init_fn, &init_circuit);
        init_eval
            .parse_literal("()")
            .map_err(|e| pretty_print(e, &smart_cookie))?;
        init_eval
            .set_literal(website_signing_key.clone())
            .map_err(|e| pretty_print(e, &smart_cookie))?;
        let mut user_state = init_eval
            .run()
            .map_err(|e| pretty_print(e, &smart_cookie))?
            .into_literal()
            .map_err(|e| pretty_print(e, &smart_cookie))?;

        for (i, interest) in interests.iter().enumerate() {
            println!("  {i}: logging '{interest}'");
            let mut log_interest_eval =
                Evaluator::new(&program, log_interest_fn, &log_interest_circuit);
            log_interest_eval
                .set_literal(user_state)
                .map_err(|e| pretty_print(e, &smart_cookie))?;
            let interest = Literal::Enum(
                "UserInterest".to_string(),
                interest.to_string(),
                VariantLiteral::Unit,
            );
            log_interest_eval
                .set_literal(Literal::Struct(
                    "WebsiteVisit".to_string(),
                    vec![
                        ("interest".to_string(), interest),
                        ("key".to_string(), website_signing_key.clone()),
                    ],
                ))
                .map_err(|e| pretty_print(e, &smart_cookie))?;
            let log_interest_result = log_interest_eval
                .run()
                .map_err(|e| pretty_print(e, &smart_cookie))?
                .into_literal()
                .map_err(|e| pretty_print(e, &smart_cookie))?;
            user_state = expect_enum(&log_interest_result, "LogResult", "Ok", Some(1))
                .pop()
                .unwrap();
        }

        let mut decide_ad_eval = Evaluator::new(&program, decide_ad_fn, &decide_ad_circuit);
        decide_ad_eval
            .set_literal(user_state)
            .map_err(|e| pretty_print(e, &smart_cookie))?;
        decide_ad_eval
            .set_literal(website_signing_key)
            .map_err(|e| pretty_print(e, &smart_cookie))?;
        let ad_decision = decide_ad_eval
            .run()
            .map_err(|e| pretty_print(e, &smart_cookie))?
            .into_literal()
            .map_err(|e| pretty_print(e, &smart_cookie))?;

        let ad_decision = expect_enum(&ad_decision, "AdDecisionResult", "Ok", Some(1));
        assert_eq!(
            ad_decision[0],
            Literal::Enum(
                "UserInterest".to_string(),
                expected_ad_decision.to_string(),
                VariantLiteral::Unit
            )
        );
    }
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
    let path = format!("./garble_examples/{file_name}");
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
