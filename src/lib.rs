use compiler::ComputeError;
use parser::{ParseError, RustishParseError};
use scanner::{scan, ScanError};
use token::MetaInfo;
use type_checker::TypeError;

use {circuit::Circuit, parser::parse};

pub mod ast;
pub mod circuit;
pub mod compiler;
pub mod env;
pub mod parser;
pub mod scanner;
pub mod token;
pub mod type_checker;
pub mod typed_ast;

pub fn compile(prg: &str) -> Result<Circuit, Error> {
    Ok(parse(prg)?.type_check()?.compile())
}

pub fn compile_rustish(prg: &str) -> Result<Circuit, Error> {
    Ok(scan(prg)?.parse()?.type_check()?.compile())
}

#[derive(Debug, Clone)]
pub enum Error {
    ScanErrors(Vec<ScanError>),
    RustishParseError(Vec<RustishParseError>),
    ParseError(ParseError),
    TypeError(TypeError),
    ComputeError(ComputeError),
}

impl From<Vec<ScanError>> for Error {
    fn from(e: Vec<ScanError>) -> Self {
        Self::ScanErrors(e)
    }
}

impl From<Vec<RustishParseError>> for Error {
    fn from(e: Vec<RustishParseError>) -> Self {
        Self::RustishParseError(e)
    }
}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Self::ParseError(e)
    }
}

impl From<TypeError> for Error {
    fn from(e: TypeError) -> Self {
        Self::TypeError(e)
    }
}

impl From<ComputeError> for Error {
    fn from(e: ComputeError) -> Self {
        Self::ComputeError(e)
    }
}

impl ParseError {
    pub fn prettify(&self, prg: &str) -> String {
        let e = Error::ParseError(self.clone());
        e.prettify(prg)
    }
}

impl TypeError {
    pub fn prettify(&self, prg: &str) -> String {
        let e = Error::TypeError(self.clone());
        e.prettify(prg)
    }
}

impl ComputeError {
    pub fn prettify(&self, prg: &str) -> String {
        let e = Error::ComputeError(self.clone());
        e.prettify(prg)
    }
}

impl Error {
    pub fn prettify(&self, prg: &str) -> String {
        let mut msg = "".to_string();
        let msg = match self {
            Error::ScanErrors(errs) => {
                for ScanError(e, meta) in errs {
                    msg += &format!(
                        "Scan error on line {}:{}\n",
                        meta.start.0 + 1,
                        meta.start.1 + 1
                    );
                    msg += &format!("--> {:?}:\n", e);
                    msg += &prettify_meta(prg, *meta);
                }
                msg
            }
            Error::RustishParseError(errs) => {
                for RustishParseError(e, meta) in errs {
                    msg += &format!(
                        "Parse error on line {}:{}\n",
                        meta.start.0 + 1,
                        meta.start.1 + 1
                    );
                    msg += &format!("--> {:?}:\n", e);
                    msg += &prettify_meta(prg, *meta);
                }
                msg
            }
            Error::ParseError(ParseError(e, meta)) => {
                msg += &format!(
                    "Parse error on line {}:{}\n",
                    meta.start.0 + 1,
                    meta.start.1 + 1
                );
                msg += &format!("--> {:?}:\n", e);
                msg += &prettify_meta(prg, *meta);
                msg
            }
            Error::TypeError(TypeError(e, meta)) => {
                msg += &format!(
                    "Type error on line {}:{}\n",
                    meta.start.0 + 1,
                    meta.start.1 + 1
                );
                msg += &format!("--> {:?}:\n", e);
                msg += &prettify_meta(prg, *meta);
                msg
            }
            Error::ComputeError(e) => format!("{:?}", e),
        };
        println!("{}", msg);
        msg
    }
}

fn prettify_meta(prg: &str, meta: MetaInfo) -> String {
    println!("meta: {:?}", meta);
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
