use crate::ast::{Expr, ExprEnum, MainDef, Op, ParamDef, Party, Program, Type};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MetaInfo {
    pub start: (usize, usize),
    pub end: (usize, usize),
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
    InvalidExpr,
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
    NumUnsigned(u128),
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
        SexprEnum::NumUnsigned(n) => ExprEnum::NumUnsigned(n),
        SexprEnum::Identifier(s) => ExprEnum::Identifier(s),
        SexprEnum::List(sexprs) => {
            if sexprs.len() == 3 {
                let mut sexprs = sexprs.into_iter();
                let (op, _meta) = expect_identifier(sexprs.next().unwrap())?;
                let op = match op.as_str() {
                    "+" => Op::Add,
                    "&" => Op::BitAnd,
                    "^" => Op::BitXor,
                    _ => {
                        return Err(ParseError(ParseErrorEnum::InvalidOp, meta));
                    }
                };
                let x = parse_expr(sexprs.next().unwrap())?;
                let y = parse_expr(sexprs.next().unwrap())?;
                ExprEnum::Op(op, Box::new(x), Box::new(y))
            } else {
                return Err(ParseError(ParseErrorEnum::InvalidExpr, meta));
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
                "u16" => Type::U16,
                "u32" => Type::U32,
                "u64" => Type::U64,
                "u128" => Type::U128,
                _ => return Err(ParseError(ParseErrorEnum::ExpectedType, meta)),
            };
            Ok((ty, meta))
        }
        Err(ParseError(_, meta)) => Err(ParseError(ParseErrorEnum::ExpectedType, meta)),
    }
}

fn parse_into_sexpr(prg: &str) -> Result<Sexpr, ParseError> {
    let mut stack = Vec::new();
    let mut stack_meta_start = Vec::new();
    let mut current_token = Vec::new();
    let mut current_token_start = (0, 0);
    for (l, line) in prg.lines().enumerate() {
        for (c, char) in line.chars().enumerate() {
            if char == '(' || char == ')' || char.is_whitespace() {
                if char == '(' {
                    stack.push(Vec::new());
                    stack_meta_start.push((l, c));
                }
                if let Some(sexprs) = stack.last_mut() {
                    if !current_token.is_empty() {
                        let token: String = current_token.iter().collect();
                        current_token.clear();
                        let meta = MetaInfo {
                            start: current_token_start,
                            end: (l, c),
                        };
                        let sexpr = if let Ok(n) = token.parse::<u128>() {
                            SexprEnum::NumUnsigned(n)
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
                    let meta = MetaInfo {
                        start: current_token_start,
                        end: (l, c),
                    };
                    return Err(ParseError(ParseErrorEnum::UnexpectedToken, meta));
                }
                if char == ')' {
                    if stack.len() > 1 {
                        if let (Some(mut sexprs), Some(parent)) = (stack.pop(), stack.last_mut()) {
                            let meta = MetaInfo {
                                start: stack_meta_start.pop().unwrap(),
                                end: (l, c + 1),
                            };
                            if sexprs.is_empty() {
                                return Err(ParseError(ParseErrorEnum::EmptySexpr, meta));
                            } else if sexprs.len() == 1 {
                                let Sexpr(sexpr, _) = sexprs.pop().unwrap();
                                parent.push(Sexpr(sexpr, meta));
                            } else {
                                parent.push(Sexpr(SexprEnum::List(sexprs), meta));
                            }
                        }
                    }
                }
            } else {
                if current_token.is_empty() {
                    current_token_start = (l, c);
                }
                current_token.push(char);
            }
        }
    }
    let meta = MetaInfo {
        start: (0, 0),
        end: (0, 1),
    };
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
    Ok(())
}
