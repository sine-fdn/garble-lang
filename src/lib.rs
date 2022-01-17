use compiler::ComputeError;
use parser::ParseError;
use type_checker::TypeError;

use {circuit::Circuit, parser::parse};

pub mod ast;
pub mod circuit;
pub mod compiler;
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

pub fn compile_with_message(prg: &str) -> Result<Circuit, String> {
    let compiled = compile(prg);
    match compiled {
        Ok(circuit) => Ok(circuit),
        Err(e) => todo!()
    }
}
