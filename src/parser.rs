use crate::ast::{Expr, ExprEnum, MainDef, Op, ParamDef, Party, Program, Type};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MetaInfo {
    //line: usize,
//column: usize,
}

#[derive(Debug, Clone)]
pub struct ParseError(pub ParseErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum ParseErrorEnum {
    EmptySexpr,
    UnexpectedToken,
    UnclosedSexpr,
    MissingMainFnDef,
    InvalidMainFnDef,
    ExpectedIdentifier,
    ExpectedListOfLength(usize),
    ExpectedKeyword(String),
    ExpectedType,
    InvalidParty,
    InvalidOp,
    BinaryExprWithInvalidNumOfArguments,
}

pub fn parse(prg: &str) -> Result<Program, ParseError> {
    let sexpr = parse_into_sexpr(prg)?;
    let ast = parse_into_ast(sexpr)?;
    Ok(ast)
}

#[derive(Debug, Clone)]
struct Sexpr(SexprEnum, MetaInfo);

#[derive(Debug, Clone)]
enum SexprEnum {
    True,
    False,
    Number(u64),
    List(Vec<Sexpr>),
    Identifier(String),
}

fn parse_into_ast(sexpr: Sexpr) -> Result<Program, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    match sexpr {
        SexprEnum::List(mut sexprs) => {
            let body = parse_expr(sexprs.pop().unwrap())?;
            let mut sexprs = sexprs.into_iter();
            if let (Some(keyword_fn), Some(identifier), Some(ty)) =
                (sexprs.next(), sexprs.next(), sexprs.next())
            {
                expect_keyword(keyword_fn, "fn")?;
                expect_keyword(identifier, "main")?;
                let (ty, _) = expect_type(ty)?;
                let mut params = Vec::new();
                while let Some(param_def) = sexprs.next() {
                    let (param_def, meta) = expect_fixed_list(param_def, 4)?;
                    let mut param_def = param_def.into_iter();
                    expect_keyword(param_def.next().unwrap(), "param")?;
                    let (identifier, _) = expect_identifier(param_def.next().unwrap())?;
                    let (party, _) = expect_identifier(param_def.next().unwrap())?;
                    let party = match party.as_str() {
                        "A" => Party::A,
                        "B" => Party::B,
                        _ => {
                            return Err(ParseError(ParseErrorEnum::InvalidParty, meta));
                        }
                    };
                    let (ty, _) = expect_type(param_def.next().unwrap())?;
                    params.push((party, ParamDef(identifier, ty)));
                }
                let fn_defs = Vec::new();
                let main = MainDef {
                    ty,
                    params,
                    body,
                    meta,
                };
                Ok(Program { fn_defs, main })
            } else {
                return Err(ParseError(ParseErrorEnum::InvalidMainFnDef, meta));
            }
        }
        _ => Err(ParseError(ParseErrorEnum::MissingMainFnDef, meta)),
    }
}

fn parse_expr(sexpr: Sexpr) -> Result<Expr, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    let expr = match sexpr {
        SexprEnum::True => ExprEnum::True,
        SexprEnum::False => ExprEnum::False,
        SexprEnum::Number(n) => ExprEnum::Number(n),
        SexprEnum::Identifier(s) => ExprEnum::Identifier(s),
        SexprEnum::List(sexprs) => {
            if sexprs.len() == 3 {
                let mut sexprs = sexprs.into_iter();
                let (op, _meta) = expect_identifier(sexprs.next().unwrap())?;
                let op = match op.as_str() {
                    "+" => Op::Add,
                    "&" => Op::BitAnd,
                    "|" => Op::BitXor,
                    _ => {
                        return Err(ParseError(ParseErrorEnum::InvalidOp, meta));
                    }
                };
                let x = parse_expr(sexprs.next().unwrap())?;
                let y = parse_expr(sexprs.next().unwrap())?;
                ExprEnum::Op(op, Box::new(x), Box::new(y))
            } else {
                return Err(ParseError(
                    ParseErrorEnum::BinaryExprWithInvalidNumOfArguments,
                    meta,
                ));
            }
        }
    };
    Ok(Expr(expr, meta))
}

fn expect_fixed_list(sexpr: Sexpr, n: usize) -> Result<(Vec<Sexpr>, MetaInfo), ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    match sexpr {
        SexprEnum::List(sexprs) => {
            if sexprs.len() == n {
                Ok((sexprs, meta))
            } else {
                Err(ParseError(ParseErrorEnum::ExpectedListOfLength(n), meta))
            }
        }
        _ => Err(ParseError(ParseErrorEnum::ExpectedListOfLength(n), meta)),
    }
}

fn expect_identifier(sexpr: Sexpr) -> Result<(String, MetaInfo), ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    match sexpr {
        SexprEnum::Identifier(s) => Ok((s, meta)),
        _ => Err(ParseError(ParseErrorEnum::ExpectedIdentifier, meta)),
    }
}

fn expect_keyword(sexpr: Sexpr, keyword: &str) -> Result<MetaInfo, ParseError> {
    match expect_identifier(sexpr) {
        Ok((identifier, meta)) => {
            if identifier == keyword {
                Ok(meta)
            } else {
                Err(ParseError(
                    ParseErrorEnum::ExpectedKeyword(keyword.to_string()),
                    meta,
                ))
            }
        }
        Err(ParseError(_, meta)) => Err(ParseError(
            ParseErrorEnum::ExpectedKeyword(keyword.to_string()),
            meta,
        )),
    }
}

fn expect_type(sexpr: Sexpr) -> Result<(Type, MetaInfo), ParseError> {
    match expect_identifier(sexpr) {
        Ok((identifier, meta)) => {
            let ty = match identifier.as_str() {
                "bool" => Type::Bool,
                "u8" => Type::U8,
                _ => return Err(ParseError(ParseErrorEnum::ExpectedType, meta)),
            };
            Ok((ty, meta))
        }
        Err(ParseError(_, meta)) => Err(ParseError(ParseErrorEnum::ExpectedType, meta)),
    }
}

fn parse_into_sexpr(prg: &str) -> Result<Sexpr, ParseError> {
    let mut stack = Vec::new();
    let mut current_token = Vec::new();
    for (_l, line) in prg.lines().enumerate() {
        for (_c, char) in line.chars().enumerate() {
            if char == '(' || char == ')' || char.is_whitespace() {
                if char == '(' {
                    stack.push(Vec::new());
                }
                if let Some(sexprs) = stack.last_mut() {
                    if current_token.is_empty() {
                    } else {
                        let token: String = current_token.iter().collect();
                        current_token.clear();
                        let meta = MetaInfo {};
                        let sexpr = if let Ok(n) = token.parse::<u64>() {
                            SexprEnum::Number(n)
                        } else if token.as_str() == "true" {
                            SexprEnum::True
                        } else if token.as_str() == "false" {
                            SexprEnum::False
                        } else {
                            SexprEnum::Identifier(token)
                        };
                        sexprs.push(Sexpr(sexpr, meta));
                    }
                } else {
                    let meta = MetaInfo {};
                    return Err(ParseError(ParseErrorEnum::UnexpectedToken, meta));
                }
                if char == ')' {
                    if stack.len() > 1 {
                        if let (Some(mut sexprs), Some(parent)) = (stack.pop(), stack.last_mut()) {
                            if sexprs.is_empty() {
                                let meta = MetaInfo {};
                                return Err(ParseError(ParseErrorEnum::EmptySexpr, meta));
                            } else if sexprs.len() == 1 {
                                parent.push(sexprs.pop().unwrap());
                            } else {
                                let meta = sexprs.first().unwrap().1;
                                parent.push(Sexpr(SexprEnum::List(sexprs), meta));
                            }
                        }
                    }
                }
            } else {
                current_token.push(char);
            }
        }
    }
    let meta = MetaInfo {};
    if stack.is_empty() {
        Err(ParseError(ParseErrorEnum::EmptySexpr, meta))
    } else if stack.len() == 1 {
        let sexprs = stack.pop().unwrap();
        let meta = sexprs.first().unwrap().1;
        Ok(Sexpr(SexprEnum::List(sexprs), meta))
    } else {
        Err(ParseError(ParseErrorEnum::UnclosedSexpr, meta))
    }
}

const prg1: &str = "
(fn main u8 (param x A u8)
  (+ x 1))
";

#[test]
fn parse_sexpr() -> Result<(), ParseError> {
    let sexpr = parse(prg1)?;
    println!("{:?}", sexpr);
    Ok(())
}
