use std::{env::args, fs::File, io::Read, process::exit};

use garble::{ast::ParamDef, check, eval::Evaluator, literal::Literal};

fn main() -> Result<(), std::io::Error> {
    let args: Vec<String> = args().collect();
    if args.len() < 3 {
        eprintln!(
            "Usage: {} file function_name [input1] [input2] ...",
            args[0]
        );
        exit(64);
    }
    let mut f = File::open(&args[1])?;
    let mut prg = String::new();
    f.read_to_string(&mut prg)?;

    let fn_name = &args[2];
    let fn_args = &args[3..];

    let program = check(&prg).unwrap_or_else(|e| {
        eprintln!("{}", e.prettify(&prg));
        exit(65);
    });
    let (circuit, main_fn) = program.compile(fn_name).unwrap_or_else(|e| {
        eprintln!("{e}");
        exit(65);
    });
    let mut evaluator = Evaluator::new(&program, &main_fn, &circuit);
    let main_params = &evaluator.main_fn.params;
    if main_params.len() != fn_args.len() {
        eprintln!(
            "Expected {} inputs, but found {}: {:?}",
            main_params.len(),
            fn_args.len(),
            fn_args
        );
        exit(65);
    }
    let mut params = Vec::with_capacity(main_params.len());
    for (i, (ParamDef(_, ty), arg)) in main_params.iter().zip(fn_args).enumerate() {
        let param = Literal::parse(&evaluator.program, &ty, arg);
        match param {
            Ok(param) => params.push(param),
            Err(e) => {
                eprintln!("Could not parse argument {i}!\n{}", e.prettify(arg));
                exit(65);
            }
        }
    }
    for param in params {
        if let Err(e) = evaluator.set_literal(param) {
            eprintln!("{}", e.prettify(&prg));
            exit(65);
        }
    }
    match evaluator.run() {
        Err(e) => {
            eprintln!("{}", e.prettify(&prg));
            exit(65);
        }
        Ok(output) => {
            let result = output.into_literal();
            match result {
                Ok(result) => {
                    println!("{}", result);
                }
                Err(e) => {
                    eprintln!("{}", e.prettify(&prg));
                    exit(70);
                }
            }
            Ok(())
        }
    }
}
