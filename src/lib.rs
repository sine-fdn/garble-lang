//! A purely functional programming language with a Rust-like syntax that compiles to logic gates
//! for secure multi-party computation.
//!
//! Garble programs always terminate and are compiled into a combination of boolean AND / XOR / NOT
//! gates. These boolean circuits can either be executed directly (mostly for testing purposes) or
//! passed to a multi-party computation engine.
//!
//! ```rust
//! use garble_lang::{compile, literal::Literal, token::UnsignedNumType::U32};
//!
//! // Compile and type-check a simple program to add the inputs of 3 parties:
//! let code = "pub fn main(x: u32, y: u32, z: u32) -> u32 { x + y + z }";
//! let prg = compile(code).map_err(|e| e.prettify(&code)).unwrap();
//!
//! // We can evaluate the circuit directly, useful for testing purposes:
//! let mut eval = prg.evaluator();
//! eval.set_u32(2);
//! eval.set_u32(10);
//! eval.set_u32(100);
//! let output = eval.run().map_err(|e| e.prettify(&code)).unwrap();
//! assert_eq!(u32::try_from(output).map_err(|e| e.prettify(&code)).unwrap(), 2 + 10 + 100);
//!
//! // Or we can run the compiled circuit in an MPC engine, simulated using `prg.circuit.eval()`:
//! let x = prg.parse_arg(0, "2").unwrap().as_bits();
//! let y = prg.parse_arg(1, "10").unwrap().as_bits();
//! let z = prg.parse_arg(2, "100").unwrap().as_bits();
//! let output = prg.circuit.eval(&[x, y, z]); // use your own MPC engine here instead
//! let result = prg.parse_output(&output).unwrap();
//! assert_eq!("112", result.to_string());
//!
//! // Input arguments can also be constructed directly as literals:
//! let x = prg.literal_arg(0, Literal::NumUnsigned(2, U32)).unwrap().as_bits();
//! let y = prg.literal_arg(1, Literal::NumUnsigned(10, U32)).unwrap().as_bits();
//! let z = prg.literal_arg(2, Literal::NumUnsigned(100, U32)).unwrap().as_bits();
//! let output = prg.circuit.eval(&[x, y, z]); // use your own MPC engine here instead
//! let result = prg.parse_output(&output).unwrap();
//! assert_eq!(Literal::NumUnsigned(112, U32), result);
//! ```

#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

use ast::{Expr, FnDef, Pattern, Program, Stmt, Type};
use check::TypeError;
use circuit::Circuit;
use compile::CompilerError;
use eval::{resolve_const_type, EvalError, Evaluator};
use literal::Literal;
use parse::ParseError;
use scan::{scan, ScanError};
use std::{
    collections::HashMap,
    fmt::{Display, Write as _},
};
use token::MetaInfo;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// [`crate::ast::Program`] without any associated type information.
pub type UntypedProgram = Program<()>;
/// [`crate::ast::FnDef`] without any associated type information.
pub type UntypedFnDef = FnDef<()>;
/// [`crate::ast::Stmt`] without any associated type information.
pub type UntypedStmt = Stmt<()>;
/// [`crate::ast::Expr`] without any associated type information.
pub type UntypedExpr = Expr<()>;
/// [`crate::ast::Pattern`] without any associated type information.
pub type UntypedPattern = Pattern<()>;

/// [`crate::ast::Program`] after typechecking.
pub type TypedProgram = Program<Type>;
/// [`crate::ast::FnDef`] after typechecking.
pub type TypedFnDef = FnDef<Type>;
/// [`crate::ast::Stmt`] after typechecking.
pub type TypedStmt = Stmt<Type>;
/// [`crate::ast::Expr`] after typechecking.
pub type TypedExpr = Expr<Type>;
/// [`crate::ast::Pattern`] after typechecking.
pub type TypedPattern = Pattern<Type>;

pub mod ast;
pub mod check;
pub mod circuit;
pub mod compile;
pub mod env;
pub mod eval;
pub mod literal;
pub mod parse;
pub mod scan;
pub mod token;

/// Scans, parses and type-checks a program.
pub fn check(prg: &str) -> Result<TypedProgram, Error> {
    Ok(scan(prg)?.parse()?.type_check()?)
}

/// Scans, parses, type-checks and then compiles the `"main"` fn of a program to a boolean circuit.
pub fn compile(prg: &str) -> Result<GarbleProgram, Error> {
    let program = check(prg)?;
    let (circuit, main) = program.compile("main")?;
    let main = main.clone();
    Ok(GarbleProgram {
        program,
        main,
        circuit,
        consts: HashMap::new(),
        const_sizes: HashMap::new(),
    })
}

/// Scans, parses, type-checks and then compiles the `"main"` fn of a program to a boolean circuit.
pub fn compile_ignore_panic(prg: &str) -> Result<GarbleProgram, Error> {
    let program = check(prg)?;
    let (circuit, main) = program.compile_ignore_panic("main")?;
    let main = main.clone();
    Ok(GarbleProgram {
        program,
        main,
        circuit,
        consts: HashMap::new(),
        const_sizes: HashMap::new(),
    })
}

/// Scans, parses, type-checks and then compiles the `"main"` fn of a program to a boolean circuit.
pub fn compile_with_constants(
    prg: &str,
    consts: HashMap<String, HashMap<String, Literal>>,
) -> Result<GarbleProgram, Error> {
    let program = check(prg)?;
    let (circuit, main, const_sizes) = program.compile_with_constants("main", consts.clone())?;
    let main = main.clone();
    Ok(GarbleProgram {
        program,
        main,
        circuit,
        consts,
        const_sizes,
    })
}

/// Scans, parses, type-checks and then compiles the `"main"` fn of a program to a boolean circuit.
pub fn compile_with_constants_ignore_panic(
    prg: &str,
    consts: HashMap<String, HashMap<String, Literal>>,
) -> Result<GarbleProgram, Error> {
    let program = check(prg)?;
    let (circuit, main, const_sizes) =
        program.compile_with_constants_ignore_panic("main", consts.clone())?;
    let main = main.clone();
    Ok(GarbleProgram {
        program,
        main,
        circuit,
        consts,
        const_sizes,
    })
}

/// The result of type-checking and compiling a Garble program.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct GarbleProgram {
    /// The type-checked represenation of the full program.
    pub program: TypedProgram,
    /// The function to be executed as a circuit.
    pub main: TypedFnDef,
    /// The compilation output, as a circuit of boolean gates.
    pub circuit: Circuit,
    /// The constants used for compiling the circuit.
    pub consts: HashMap<String, HashMap<String, Literal>>,
    /// The values of usize constants used for compiling the circuit.
    pub const_sizes: HashMap<String, usize>,
}

/// An input argument for a Garble program and circuit.
#[derive(Debug, Clone)]
pub struct GarbleArgument<'a>(Literal, &'a TypedProgram, &'a HashMap<String, usize>);

impl GarbleProgram {
    /// Returns an evaluator that can be used to run the compiled circuit.
    pub fn evaluator(&self) -> Evaluator<'_> {
        Evaluator::new(&self.program, &self.main, &self.circuit, &self.const_sizes)
    }

    /// Type-checks and uses the literal as the circuit input argument with the given index.
    pub fn literal_arg(
        &self,
        arg_index: usize,
        literal: Literal,
    ) -> Result<GarbleArgument<'_>, EvalError> {
        let Some(param) = self.main.params.get(arg_index) else {
            return Err(EvalError::InvalidArgIndex(arg_index));
        };
        let ty = resolve_const_type(&param.ty, &self.const_sizes);
        if !literal.is_of_type(&self.program, &ty) {
            return Err(EvalError::InvalidLiteralType(literal, ty));
        }
        Ok(GarbleArgument(literal, &self.program, &self.const_sizes))
    }

    /// Tries to parse the string as the circuit input argument with the given index.
    pub fn parse_arg(
        &self,
        arg_index: usize,
        literal: &str,
    ) -> Result<GarbleArgument<'_>, EvalError> {
        let Some(param) = self.main.params.get(arg_index) else {
            return Err(EvalError::InvalidArgIndex(arg_index));
        };
        let literal = Literal::parse(&self.program, &param.ty, literal)
            .map_err(EvalError::LiteralParseError)?;
        Ok(GarbleArgument(literal, &self.program, &self.const_sizes))
    }

    /// Tries to convert the circuit output back to a Garble literal.
    pub fn parse_output(&self, bits: &[bool]) -> Result<Literal, EvalError> {
        Literal::from_result_bits(&self.program, &self.main.ty, bits, &self.const_sizes)
    }
}

impl GarbleArgument<'_> {
    /// Converts the argument to input bits for the compiled circuit.
    pub fn as_bits(&self) -> Vec<bool> {
        self.0.as_bits(self.1, self.2)
    }

    /// Converts the argument to a Garble literal.
    pub fn as_literal(&self) -> Literal {
        self.0.clone()
    }
}

impl Display for GarbleArgument<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Errors that can occur during compile time, while a program is scanned, parsed or type-checked.
#[derive(Debug, Clone)]
pub enum CompileTimeError {
    /// Errors originating in the scanning phase.
    ScanErrors(Vec<ScanError>),
    /// Errors originating in the parsing phase.
    ParseError(Vec<ParseError>),
    /// Errors originating in the type-checking phase.
    TypeError(Vec<TypeError>),
    /// Errors originating in the compilation phase.
    CompilerError(Vec<CompilerError>),
}

/// A generic error that combines compile-time and run-time errors.
#[derive(Debug, Clone)]
pub enum Error {
    /// The specified function was not found in the source code.
    FnNotFound(String),
    /// Errors occurring during compile time.
    CompileTimeError(CompileTimeError),
    /// Errors occurring during the run-time evaluation of the circuit.
    EvalError(EvalError),
}

impl From<Vec<ScanError>> for CompileTimeError {
    fn from(e: Vec<ScanError>) -> Self {
        Self::ScanErrors(e)
    }
}

impl From<Vec<ParseError>> for CompileTimeError {
    fn from(e: Vec<ParseError>) -> Self {
        Self::ParseError(e)
    }
}

impl From<Vec<TypeError>> for CompileTimeError {
    fn from(e: Vec<TypeError>) -> Self {
        Self::TypeError(e)
    }
}

impl From<Vec<CompilerError>> for CompileTimeError {
    fn from(e: Vec<CompilerError>) -> Self {
        Self::CompilerError(e)
    }
}

impl<E: Into<CompileTimeError>> From<E> for Error {
    fn from(e: E) -> Self {
        Error::CompileTimeError(e.into())
    }
}

impl From<EvalError> for Error {
    fn from(e: EvalError) -> Self {
        Self::EvalError(e)
    }
}

impl EvalError {
    /// Returns a human-readable error description, showing where the error occurred in the source.
    pub fn prettify(&self, prg: &str) -> String {
        match self {
            EvalError::Panic(panic) => {
                let mut msg = "".to_string();
                let meta = panic.panicked_at;
                writeln!(
                    msg,
                    "Panic due to {} on line {}:{}.\n",
                    panic.reason,
                    meta.start.0 + 1,
                    meta.start.1 + 1
                )
                .unwrap();
                msg += &prettify_meta(prg, meta);
                msg
            }
            _ => format!("{self}"),
        }
    }
}

impl Error {
    /// Returns a human-readable error description, showing where the error occurred in the source.
    pub fn prettify(&self, prg: &str) -> String {
        match self {
            Error::FnNotFound(fn_name) => {
                format!("Could not find any function with name '{fn_name}'")
            }
            Error::CompileTimeError(e) => e.prettify(prg),
            Error::EvalError(e) => e.prettify(prg),
        }
    }
}

impl CompileTimeError {
    /// Returns a human-readable error description, showing where the error occurred in the source.
    pub fn prettify(&self, prg: &str) -> String {
        let mut errs_for_display = vec![];
        match self {
            CompileTimeError::ScanErrors(errs) => {
                for ScanError(e, meta) in errs {
                    errs_for_display.push(("Scan error", format!("{e}"), Some(*meta)));
                }
            }
            CompileTimeError::ParseError(errs) => {
                for ParseError(e, meta) in errs {
                    errs_for_display.push(("Parse error", format!("{e}"), Some(*meta)));
                }
            }
            CompileTimeError::TypeError(errs) => {
                for TypeError(e, meta) in errs {
                    errs_for_display.push(("Type error", format!("{e}"), Some(*meta)));
                }
            }
            CompileTimeError::CompilerError(errs) => {
                for e in errs {
                    match e {
                        CompilerError::MissingConstant(_, _, meta) => {
                            errs_for_display.push(("Compiler error", format!("{e}"), Some(*meta)))
                        }
                        e => errs_for_display.push(("Compiler error", format!("{e}"), None)),
                    }
                }
            }
        }
        let mut msg = "".to_string();
        for (err_type, err, meta) in errs_for_display {
            if let Some(meta) = meta {
                writeln!(
                    msg,
                    "\n{} on line {}:{}.",
                    err_type,
                    meta.start.0 + 1,
                    meta.start.1 + 1
                )
                .unwrap();
            } else {
                writeln!(msg, "\n{}:", err_type).unwrap();
            }
            writeln!(msg, "{err}:").unwrap();
            if let Some(meta) = meta {
                msg += &prettify_meta(prg, meta);
            }
        }
        msg
    }
}

fn prettify_meta(prg: &str, meta: MetaInfo) -> String {
    let mut msg = "".to_string();
    if prg.is_empty() {
        return msg;
    }
    let lines: Vec<&str> = prg.lines().collect();
    for l in (meta.start.0 as i64 - 2)..(meta.end.0 as i64 + 2) {
        let line_start = meta.start.0 as i64;
        let line_end = meta.end.0 as i64;
        let line_should_be_highlighted =
            l >= line_start && (l < line_end || (l == line_end && meta.end.1 > 0));
        if l >= 0 && (l as usize) < lines.len() {
            if line_should_be_highlighted {
                writeln!(msg, "{: >4} > | {}", l + 1, lines[l as usize]).unwrap();
            } else {
                writeln!(msg, "       | {}", lines[l as usize]).unwrap();
            }
        }
        if line_should_be_highlighted {
            msg += "     > | ";
            let col_start = if l == line_start { meta.start.1 } else { 0 };
            let col_end = if l == line_end {
                meta.end.1
            } else {
                lines[l as usize].len()
            };
            for _ in 0..col_start {
                msg += " ";
            }
            for _ in col_start..col_end {
                msg += "^";
            }
            msg += "\n";
        }
    }
    msg
}
