use garble_lang::{ast::Type, check, circuit::Circuit, eval::Evaluator, literal::Literal, Error};

#[test]
// Tests whether successive compilations always result in the same circuit, rather than different circuits with the same
// output
fn credit_scoring_multiple_compilations() -> Result<(), Error> {
    let credit_scoring = include_str!("../garble_examples/credit_scoring.garble.rs");
    println!("Parsing and type-checking...");
    let typed_prg = check(&credit_scoring).map_err(|e| pretty_print(e, &credit_scoring))?;
    println!("Compiling...");
    let mut circuit: Option<Circuit> = None;

    for _ in 0..4 {
        let (compute_score_circuit, _) = typed_prg.compile("compute_score")?;
        println!(
            ">> 'compute_score' has {}",
            compute_score_circuit.report_gates()
        );
        if let Some(prev_compilation) = circuit {
            if format!("{:?}", compute_score_circuit) != format!("{:?}", prev_compilation) {
                println!(
                    "{} vs {} gates",
                    compute_score_circuit.gates.len(),
                    prev_compilation.gates.len()
                );
                for (i, (g1, g2)) in compute_score_circuit
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
        circuit = Some(compute_score_circuit);
    }
    Ok(())
}

#[test]
fn credit_scoring_single_run() -> Result<(), Error> {
  let credit_scoring = include_str!("../garble_examples/credit_scoring.garble.rs");
  println!("Parsing and type-checking...");
    let typed_prg = check(&credit_scoring).map_err(|e| pretty_print(e, &credit_scoring))?;
    println!("Compiling...");

    let user_ty = Type::Struct("User".to_string());
    let user = Literal::parse(
        &typed_prg,
        &user_ty,
        "User {
          age: 37u8,
          income: 5500u32,
          account_balance: 25000i64,
          current_loans: 60000u64,
          credit_card_limit: 1000u32,
          ever_bankrupt: false,
          loan_payment_failures: 0u8,
          credit_payment_failures: 2u8,
          surety_income: 5000u32
        }",
    )?;

    let scoring_algorithm_ty = Type::Struct("ScoringAlgorithm".to_string());
    let scoring_algorithm = Literal::parse(
        &typed_prg,
        &scoring_algorithm_ty,
        "ScoringAlgorithm {
          age_score: [
            MatchClause::Range(Range {min: 0i64, max: 18i64}, Points {inc: 0i32}),
            MatchClause::Range(Range {min: 18i64, max: 35i64}, Points {inc: 50i32}),
            MatchClause::Range(Range {min: 35i64, max: 65i64}, Points {inc: 100i32}),
            MatchClause::Range(Range {min: 65i64, max: 120i64}, Points {inc: 50i32})
            ],
          income_score: [
            MatchClause::Range(Range {min: 2000i64, max: 5000i64}, Points {inc: 50i32}),
            MatchClause::Range(Range {min: 5000i64, max: 10000i64}, Points {inc: 100i32}),
            MatchClause::Range(Range {min: 10000i64, max: 999999999i64}, Points {inc: 200i32}),
            MatchClause::None
            ],
          account_balance_score: [
            MatchClause::Range(Range {min: -999999999i64, max: 0i64}, Points {inc: -100i32}),
            MatchClause::Range(Range {min: 0i64, max:5000i64}, Points {inc: 0i32}),
            MatchClause::Range(Range {min: 5000i64, max: 10000i64}, Points {inc: 50i32}),
            MatchClause::Range(Range {min: 10000i64, max: 999999999i64}, Points {inc: 200i32})
            ],
          current_loans_score: [
            MatchClause::Range(Range {min:500000i64, max: 100000000i64}, Points {inc: 0i32}),
            MatchClause::Range(Range {min:100000i64, max: 500000i64}, Points {inc: 150i32}),
            MatchClause::Range(Range {min:0i64, max: 100000i64}, Points {inc: 300i32}),
            MatchClause::None],
          credit_card_score: [
            MatchClause::Range(Range {min: 0i64, max: 10000i64}, Points {inc: 100i32}),
            MatchClause::None,
            MatchClause::None,
            MatchClause::None
            ],
          bankruptcy_score: [
            MatchClause::Bool(true, Points {inc: -100i32}),
            MatchClause::Bool(false, Points {inc: 50i32})
            ],
          loan_payment_history_score: [
            MatchClause::Range(Range {min: 0i64, max: 3i64}, Points {inc: 0i32}),
            MatchClause::Range(Range {min: 3i64, max: 6i64}, Points {inc: -100i32}),
            MatchClause::None,
            MatchClause::None
            ],
          credit_payment_history_score: [
            MatchClause::Range(Range {min: 0i64, max: 1i64}, Points {inc: 0i32}),
            MatchClause::Range(Range {min: 1i64, max: 3i64}, Points {inc: -100i32}),
            MatchClause::Range(Range {min: 3i64, max: 6i64}, Points {inc: -200i32}),
            MatchClause::None
            ],
          surety_income_score: [
            MatchClause::Range(Range {min: 0i64, max: 1000i64}, Points {inc: -50i32}),
            MatchClause::Range(Range {min: 1000i64, max: 5000i64}, Points {inc: 0i32}),
            MatchClause::Range(Range {min: 5000i64, max: 10000i64}, Points {inc: 100i32}),
            MatchClause::None
            ],
          score_limits: ScoreLimits {min: 0i32, max: 1000i32}
        }",
    )?;

    let (compute_score_circuit, compute_score_fn) = typed_prg.compile("compute_score")?;
    let mut eval = Evaluator::new(&typed_prg, &compute_score_fn, &compute_score_circuit);

    eval.set_literal(scoring_algorithm)?;
    eval.set_literal(user)?;
    let output = eval.run().map_err(|e| pretty_print(e, &credit_scoring))?;
    let r = output
        .into_literal()
        .map_err(|e| pretty_print(e, &credit_scoring))?;

    let score_ty = Type::Enum("Score".to_string());
    let expected = Literal::parse(&typed_prg, &score_ty, "Score::Good(85u8)")?;
    assert_eq!(r, expected);
    Ok(())
}

fn pretty_print<E: Into<Error>>(e: E, prg: &str) -> Error {
    let e: Error = e.into();
    let pretty = e.prettify(prg);
    println!("{}", pretty);
    e
}
