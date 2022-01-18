use compiler::ComputeError;
use parser::{MetaInfo, ParseError};
use type_checker::TypeError;

use {circuit::Circuit, parser::parse};

pub mod ast;
pub mod circuit;
pub mod compiler;
pub mod env;
pub mod parser;
pub mod type_checker;
pub mod typed_ast;

#[derive(Debug, Clone)]
pub enum Error {
    ParseError(ParseError),
    TypeError(TypeError),
    ComputeError(ComputeError),
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

pub fn compile(prg: &str) -> Result<Circuit, Error> {
    Ok(parse(prg)?.type_check()?.compile())
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
            Error::ComputeError(e) => format!("{:?}", e)
        };
        println!("{}", msg);
        msg
    }
}

fn prettify_meta(prg: &str, meta: MetaInfo) -> String {
    let mut msg = "".to_string();
    let lines: Vec<&str> = prg.lines().collect();
    for l in (meta.start.0 as i64 - 2)..(meta.start.0 as i64 + 2) {
        let line_start = meta.start.0 as i64;
        let line_end = meta.end.0 as i64;
        if l >= 0 && (l as usize) < lines.len() {
            if l >= line_start && l <= line_end {
                msg += &format!("{: >4} > | {}\n", l + 1, lines[l as usize]);
            } else {
                msg += &format!("       | {}\n", lines[l as usize]);
            }
        }
        if l >= line_start && l <= line_end {
            msg += "     > | ";
            let col_start = if l == line_start {
                meta.start.1
            } else {
                0
            };
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
