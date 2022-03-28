//! A purely functional programming language with a Rust-like syntax that compiles to logic gates
//! for secure multi-party computation.

#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

use check::TypeError;
use compile::CompilerError;
use eval::EvalError;
use parse::ParseError;
use scan::{scan, ScanError};
use token::MetaInfo;

use circuit::Circuit;
use typed_ast::{FnDef, Program};

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
pub mod typed_ast;

/// Scans, parses and type-checks a program.
pub fn check(prg: &str) -> Result<Program, Error> {
    Ok(scan(prg)?.parse()?.type_check()?)
}

/// Scans, parses, type-checks and then compiles a program to a circuit of gates.
pub fn compile(prg: &str, fn_name: &str) -> Result<(Program, FnDef, Circuit), Error> {
    let program = check(prg)?;
    let (circuit, main_fn) = program.compile(fn_name)?;
    let main_fn = main_fn.clone();
    Ok((program, main_fn, circuit))
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
    CompilerError(CompilerError),
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

impl From<CompilerError> for CompileTimeError {
    fn from(e: CompilerError) -> Self {
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
                msg += &format!(
                    "Panic due to {} on line {}:{}.\n\n",
                    panic.reason,
                    meta.start.0 + 1,
                    meta.start.1 + 1
                );
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
                    errs_for_display.push(("Scan error", format!("{e}"), *meta));
                }
            }
            CompileTimeError::ParseError(errs) => {
                for ParseError(e, meta) in errs {
                    errs_for_display.push(("Parse error", format!("{e}"), *meta));
                }
            }
            CompileTimeError::TypeError(errs) => {
                for TypeError(e, meta) in errs {
                    errs_for_display.push(("Type error", format!("{e}"), *meta));
                }
            }
            CompileTimeError::CompilerError(e) => {
                let meta = MetaInfo {
                    start: (0, 0),
                    end: (0, 0),
                };
                errs_for_display.push(("Compiler error", format!("{e}"), meta))
            }
        }
        let mut msg = "".to_string();
        for (err_type, err, meta) in errs_for_display {
            msg += &format!(
                "{} on line {}:{}.\n",
                err_type,
                meta.start.0 + 1,
                meta.start.1 + 1
            );
            msg += &format!("{}:\n\n", err);
            msg += &prettify_meta(prg, meta);
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
                msg += &format!("{: >4} > | {}\n", l + 1, lines[l as usize]);
            } else {
                msg += &format!("       | {}\n", lines[l as usize]);
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
