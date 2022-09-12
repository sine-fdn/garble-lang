use std::{fs::File, io::Read, path::PathBuf, process::exit};

use garble_lang::{ast::ParamDef, check, eval::Evaluator, literal::Literal};

use clap::{Parser, Subcommand};

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Type-checks, compiles and runs garble program
    /// usage: garble run [OPTIONS] <FILE> <INPUTS>...
    #[clap(verbatim_doc_comment)]
    Run {
        /// Provide the path to the garble.rs file where your program is written
        #[clap(value_parser)]
        file: PathBuf,

        /// Provide inputs to be passed as arguments in your function
        #[clap(value_parser, required = true)]
        inputs: Vec<String>,

        /// Specify the name of the function to be ran
        #[clap(short, long, value_parser, default_value = "main", alias = "fn")]
        function: String,
    },
    /// Type-checks garble program
    /// usage: garble check <FILE>
    #[clap(verbatim_doc_comment)]
    Check {
        /// Provide the path to the garble.rs file where your program is written
        #[clap(value_parser)]
        file: PathBuf,
    },
}

fn main() -> Result<(), std::io::Error> {
    let args = Args::parse();

    match args.command {
        Command::Run {
            file,
            inputs,
            function,
        } => run(file, inputs, function),
        Command::Check { file } => type_check(file),
    }
}

fn run(file: PathBuf, inputs: Vec<String>, function: String) -> Result<(), std::io::Error> {
    let mut f = File::open(&file).unwrap_or_else(|_| {
        eprintln!("Couldn't find {:?}", file);
        exit(65);
    });
    let mut prg = String::new();
    f.read_to_string(&mut prg)?;

    let program = check(&prg).unwrap_or_else(|e| {
        eprintln!("{}", e.prettify(&prg));
        exit(65);
    });
    let (circuit, main_fn) = program.compile(&function).unwrap_or_else(|e| {
        eprintln!("{e}");
        exit(65);
    });

    let mut arguments: Vec<String> = Vec::with_capacity(inputs.len());

    for input in inputs.into_iter() {
        let input = match File::open(&input) {
            Ok(mut file) => {
                let mut argument = String::new();
                file.read_to_string(&mut argument).unwrap_or_else(|e| {
                    eprintln!("{e}");
                    exit(65)
                });
                argument
            }
            Err(_) => input,
        };
        arguments.push(input);
    }

    let mut evaluator = Evaluator::new(&program, main_fn, &circuit);
    let main_params = &evaluator.main_fn.params;
    if main_params.len() != arguments.len() {
        eprintln!(
            "Expected {} inputs, but found {}: {:?}",
            main_params.len(),
            arguments.len(),
            arguments
        );
        exit(65);
    }
    let mut params = Vec::with_capacity(main_params.len());
    for (i, (ParamDef(_, _, ty), input)) in main_params.iter().zip(arguments).enumerate() {
        let param = Literal::parse(&program, ty, &input);
        match param {
            Ok(param) => params.push(param),
            Err(e) => {
                eprintln!("Input {i} is not of type {ty}!\n{}", e.prettify(&input));
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

fn type_check(file: PathBuf) -> Result<(), std::io::Error> {
    let mut f = File::open(&file).unwrap_or_else(|_| {
        eprintln!("Couldn't find {:?}", file);
        exit(65);
    });
    let mut prg = String::new();
    f.read_to_string(&mut prg)?;

    match check(&prg) {
        Err(e) => {
            eprintln!("{}", e.prettify(&prg));
            exit(65);
        }
        Ok(_) => {
            println!("No type errors in the program.");
            Ok(())
        }
    }
}
