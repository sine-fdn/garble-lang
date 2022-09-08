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
    /// Check, compile and run garble program
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
}

fn main() -> Result<(), std::io::Error> {
    let args = Args::parse();

    match &args.command {
        Command::Run {
            file,
            inputs,
            function: fn_name,
        } => run(file, inputs, fn_name),
    }
}

fn run(file: &PathBuf, inputs: &Vec<String>, fn_name: &String) -> Result<(), std::io::Error> {
    let mut f = File::open(file).unwrap_or_else(|e| {
        eprintln!(
            "Couldn't find {:?}. Please make sure it is the right file path.\nError: {e}",
            file
        );
        exit(65);
    });
    let mut prg = String::new();
    f.read_to_string(&mut prg)?;

    let program = check(&prg).unwrap_or_else(|e| {
        eprintln!("{}", e.prettify(&prg));
        exit(65);
    });
    let (circuit, main_fn) = program.compile(fn_name).unwrap_or_else(|e| {
        eprintln!("{e}");
        exit(65);
    });
    let mut evaluator = Evaluator::new(&program, main_fn, &circuit);
    let main_params = &evaluator.main_fn.params;
    if main_params.len() != inputs.len() {
        eprintln!(
            "Expected {} inputs, but found {}: {:?}",
            main_params.len(),
            inputs.len(),
            inputs
        );
        exit(65);
    }
    let mut params = Vec::with_capacity(main_params.len());
    for (i, (ParamDef(_, _, ty), input)) in main_params.iter().zip(inputs).enumerate() {
        let param = Literal::parse(&program, ty, input);
        match param {
            Ok(param) => params.push(param),
            Err(e) => {
                eprintln!("Input {i} is not of type {ty}!\n{}", e.prettify(input));
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
