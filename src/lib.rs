use check::TypeError;
use eval::EvalError;
use parse::ParseError;
use scan::{scan, ScanError};
use token::MetaInfo;

use circuit::Circuit;

pub mod ast;
pub mod check;
pub mod circuit;
pub mod compile;
pub mod env;
pub mod eval;
pub mod parse;
pub mod scan;
pub mod token;
pub mod typed_ast;

pub fn compile(prg: &str) -> Result<Circuit, Error> {
    Ok(scan(prg)?.parse()?.type_check()?.compile())
}

#[derive(Debug, Clone)]
pub enum CompileTimeError {
    ScanErrors(Vec<ScanError>),
    ParseError(Vec<ParseError>),
    TypeError(TypeError),
}

#[derive(Debug, Clone)]
pub enum Error {
    CompileTimeError(CompileTimeError),
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

impl From<TypeError> for CompileTimeError {
    fn from(e: TypeError) -> Self {
        Self::TypeError(e)
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

impl TypeError {
    pub fn prettify(&self, prg: &str) -> String {
        let e = CompileTimeError::TypeError(self.clone());
        e.prettify(prg)
    }
}

impl EvalError {
    pub fn prettify(&self, prg: &str) -> String {
        let e = Error::EvalError(self.clone());
        e.prettify(prg)
    }
}

impl Error {
    pub fn prettify(&self, prg: &str) -> String {
        match self {
            Error::CompileTimeError(e) => e.prettify(prg),
            Error::EvalError(e) => format!("{:?}", e),
        }
    }
}

impl CompileTimeError {
    pub fn prettify(&self, prg: &str) -> String {
        let mut errs_for_display = vec![];
        match self {
            CompileTimeError::ScanErrors(errs) => {
                for ScanError(e, meta) in errs {
                    errs_for_display.push(("Scan error", format!("{:?}", e), meta));
                }
            }
            CompileTimeError::ParseError(errs) => {
                for ParseError(e, meta) in errs {
                    errs_for_display.push(("Parse error", format!("{:?}", e), meta));
                }
            }
            CompileTimeError::TypeError(TypeError(e, meta)) => {
                errs_for_display.push(("Type error", format!("{:?}", e), meta));
            }
        }
        let mut msg = "".to_string();
        for (err_type, err, meta) in errs_for_display {
            msg += &format!(
                "{} on line {}:{}\n",
                err_type,
                meta.start.0 + 1,
                meta.start.1 + 1
            );
            msg += &format!("--> {}:\n", err);
            msg += &prettify_meta(prg, *meta);
        }
        println!("{}", msg);
        msg
    }
}

fn prettify_meta(prg: &str, meta: MetaInfo) -> String {
    let mut msg = "".to_string();
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
