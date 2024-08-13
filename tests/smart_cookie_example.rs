use std::collections::HashMap;

use garble_lang::{
    check,
    circuit::Circuit,
    eval::Evaluator,
    literal::{Literal, VariantLiteral},
    token::UnsignedNumType,
    Error,
};

#[test]
fn smart_cookie_compilation() -> Result<(), Error> {
    let smart_cookie = include_str!("../garble_examples/smart_cookie.garble.rs");
    println!("Parsing and type-checking...");
    let program = check(smart_cookie).map_err(|e| pretty_print(e, smart_cookie))?;
    println!("Compiling...");

    let mut circuit: Option<Circuit> = None;
    for _ in 0..4 {
        let (decide_ad_circuit, _) = program.compile("decide_ad")?;
        println!(">> 'decide_ad' has {}", decide_ad_circuit.report_gates());
        if let Some(prev_compilation) = circuit {
            if format!("{decide_ad_circuit:?}") != format!("{prev_compilation:?}") {
                println!(
                    "{} vs {} gates",
                    decide_ad_circuit.gates.len(),
                    prev_compilation.gates.len()
                );
                for (i, (g1, g2)) in decide_ad_circuit
                    .gates
                    .iter()
                    .zip(prev_compilation.gates.iter())
                    .enumerate()
                {
                    if g1 != g2 {
                        println!("Mismatch at {i}: {g1:?} vs {g2:?}");
                    }
                }
                panic!("Circuit mismatch!");
            }
        }
        circuit = Some(decide_ad_circuit);
    }
    Ok(())
}

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
            .chain(["Luxury"; 40])
            .collect::<Vec<_>>(),
    );

    for (expected_ad_decision, interests) in [interests1, interests2] {
        let smart_cookie = include_str!("../garble_examples/smart_cookie.garble.rs");
        println!("Parsing and type-checking...");
        let program = check(smart_cookie).map_err(|e| pretty_print(e, smart_cookie))?;
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
                        .map(|byte| Literal::NumUnsigned(*byte as u64, UnsignedNumType::U8))
                        .collect(),
                ),
            )],
        );

        let const_sizes = HashMap::new();
        let mut init_eval = Evaluator::new(&program, init_fn, &init_circuit, &const_sizes);
        init_eval
            .set_literal(website_signing_key.clone())
            .map_err(|e| pretty_print(e, smart_cookie))?;
        init_eval
            .parse_literal("()")
            .map_err(|e| pretty_print(e, smart_cookie))?;
        let mut user_state = init_eval
            .run()
            .map_err(|e| pretty_print(e, smart_cookie))?
            .into_literal()
            .map_err(|e| pretty_print(e, smart_cookie))?;

        for (i, interest) in interests.iter().enumerate() {
            println!("  {i}: logging '{interest}'");
            let mut log_interest_eval = Evaluator::new(
                &program,
                log_interest_fn,
                &log_interest_circuit,
                &const_sizes,
            );
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
                .map_err(|e| pretty_print(e, smart_cookie))?;
            log_interest_eval
                .set_literal(user_state)
                .map_err(|e| pretty_print(e, smart_cookie))?;
            let log_interest_result = log_interest_eval
                .run()
                .map_err(|e| pretty_print(e, smart_cookie))?
                .into_literal()
                .map_err(|e| pretty_print(e, smart_cookie))?;
            user_state = expect_enum(&log_interest_result, "LogResult", "Ok", Some(1))
                .pop()
                .unwrap();
        }

        let mut decide_ad_eval =
            Evaluator::new(&program, decide_ad_fn, &decide_ad_circuit, &const_sizes);
        decide_ad_eval
            .set_literal(website_signing_key)
            .map_err(|e| pretty_print(e, smart_cookie))?;
        decide_ad_eval
            .set_literal(user_state)
            .map_err(|e| pretty_print(e, smart_cookie))?;
        let ad_decision = decide_ad_eval
            .run()
            .map_err(|e| pretty_print(e, smart_cookie))?
            .into_literal()
            .map_err(|e| pretty_print(e, smart_cookie))?;

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

fn pretty_print<E: Into<Error>>(e: E, prg: &str) -> Error {
    let e: Error = e.into();
    let pretty = e.prettify(prg);
    println!("{pretty}");
    e
}
