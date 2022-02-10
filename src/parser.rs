use std::{iter::Peekable, vec::IntoIter};

use crate::{
    ast::{
        Closure, EnumDef, Expr, ExprEnum, FnDef, MainDef, Op, ParamDef, Party, Pattern,
        PatternEnum, Program, Type, UnaryOp, Variant, VariantExpr, VariantExprEnum,
    },
    scanner::Tokens,
    token::{MetaInfo, Token, TokenEnum},
};

#[derive(Debug, Clone)]
pub struct ParseError(pub ParseErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]
pub enum ParseErrorEnum {
    EmptySexpr,
    UnexpectedToken,
    UnclosedSexpr,
    InvalidDef,
    InvalidEnumDef,
    InvalidFnDef,
    InvalidMainFnDef,
    InvalidEnumVariant,
    InvalidEnumPattern,
    InvalidEnumPatternEnum,
    InvalidRangePattern,
    InvalidPattern,
    ExpectedIdentifier,
    ExpectedListOfLength(usize),
    ExpectedKeyword(String),
    ExpectedType,
    InvalidParty,
    InvalidArity(usize),
    InvalidExpr,
    ArrayMaxSizeExceeded(u128),
    TupleMaxSizeExceeded(u128),
}

#[derive(Debug, Clone)]
pub struct RustishParseError(pub RustishParseErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]

pub enum RustishParseErrorEnum {
    MissingMainFnDef,
    InvalidTopLevelDef,
    InvalidParty,
    InvalidArraySize,
    InvalidTupleIndexSize,
    InvalidMethodName,
    InvalidRangeExpr,
    InvalidPattern,
    ExpectedConstantArraySize,
    ExpectedType,
    ExpectedExpr,
    ExpectedIdentifier,
    ExpectedMethodCallOrFieldAccess,
    UnexpectedToken,
}

impl Tokens {
    pub fn parse(self) -> Result<Program, Vec<RustishParseError>> {
        Parser::new(self.0).parse()
    }
}

struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    errors: Vec<RustishParseError>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: vec![],
        }
    }

    fn parse(mut self) -> Result<Program, Vec<RustishParseError>> {
        let top_level_keywords = [TokenEnum::KeywordFn];
        let mut enum_defs = vec![];
        let mut fn_defs = vec![];
        let mut main_fn_def = None;
        let mut has_main = false;
        while let Some(Token(token_enum, meta)) = self.tokens.next() {
            match token_enum {
                TokenEnum::KeywordEnum => {
                    if let Ok(enum_def) = self.parse_enum_def(meta) {
                        enum_defs.push(enum_def);
                    } else {
                        self.consume_until_one_of(&top_level_keywords);
                    }
                }
                TokenEnum::KeywordFn => {
                    if let Some(Token(TokenEnum::Identifier(fn_name), _)) = self.tokens.peek() {
                        if fn_name.as_str() == "main" {
                            has_main = true;
                            if let Ok(main_def) = self.parse_main_fn_def(meta) {
                                main_fn_def = Some(main_def);
                            } else {
                                self.consume_until_one_of(&top_level_keywords);
                            }
                        } else {
                            if let Ok(fn_def) = self.parse_fn_def(meta) {
                                fn_defs.push(fn_def);
                            } else {
                                self.consume_until_one_of(&top_level_keywords);
                            }
                        }
                    }
                }
                _ => {
                    self.push_error(RustishParseErrorEnum::InvalidTopLevelDef, meta);
                    self.consume_until_one_of(&top_level_keywords);
                }
            }
        }
        if let Some(main) = main_fn_def {
            Ok(Program {
                enum_defs,
                fn_defs,
                main,
            })
        } else {
            if !has_main {
                let meta = MetaInfo {
                    start: (0, 0),
                    end: (0, 0),
                };
                self.push_error(RustishParseErrorEnum::MissingMainFnDef, meta);
            }
            Err(self.errors)
        }
    }

    fn parse_enum_def(&mut self, start: MetaInfo) -> Result<EnumDef, ()> {
        // enum keyword was already consumed by the top-level parser

        let (identifier, _) = self.expect_identifier()?;

        self.expect(&TokenEnum::LeftBrace)?;

        let mut variants = vec![self.parse_variant()?];

        while let Some(_) = self.next_matches(&TokenEnum::Comma) {
            if let Some(Token(TokenEnum::Identifier(_), _)) = self.tokens.peek() {
                variants.push(self.parse_variant()?);
            }
        }

        let end = self.expect(&TokenEnum::RightBrace)?;
        let meta = join_meta(start, end);
        Ok(EnumDef {
            identifier,
            variants,
            meta,
        })
    }

    fn parse_variant(&mut self) -> Result<Variant, ()> {
        let (variant_name, _) = self.expect_identifier()?;
        if let Some(_) = self.next_matches(&TokenEnum::LeftParen) {
            let mut fields = vec![];
            if let Some(Token(TokenEnum::Identifier(_), _)) = self.tokens.peek() {
                let (ty, _) = self.parse_type()?;
                fields.push(ty);
            }
            while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                let (ty, _) = self.parse_type()?;
                fields.push(ty);
            }
            self.expect(&TokenEnum::RightParen)?;
            Ok(Variant::Tuple(variant_name, fields))
        } else {
            Ok(Variant::Unit(variant_name))
        }
    }

    fn parse_fn_def(&mut self, start: MetaInfo) -> Result<FnDef, ()> {
        // fn keyword was already consumed by the top-level parser

        let (identifier, _) = self.expect_identifier()?;

        // ( ... )
        self.expect(&TokenEnum::LeftParen)?;
        let mut params = vec![];
        if !self.peek(&TokenEnum::RightParen) {
            params.extend(self.parse_params()?);
            self.expect(&TokenEnum::RightParen)?;
        } else {
            self.expect(&TokenEnum::RightParen)?;
        }

        // -> <ty>
        self.expect(&TokenEnum::Arrow)?;
        let (ty, _) = self.parse_type()?;

        // { ... }
        self.expect(&TokenEnum::LeftBrace)?;
        let body = self.parse_expr()?;
        let end = self.expect(&TokenEnum::RightBrace)?;

        let meta = join_meta(start, end);
        Ok(FnDef {
            ty,
            identifier,
            params,
            body,
            meta,
        })
    }

    fn parse_main_fn_def(&mut self, start: MetaInfo) -> Result<MainDef, ()> {
        // fn keyword was already consumed by the top-level parser
        let (fn_name, _) = self.expect_identifier()?;
        if fn_name.as_str() != "main" {
            panic!("this function should not have been called on a non-main fn def");
        }

        // ( ... )
        self.expect(&TokenEnum::LeftParen)?;
        let mut params = vec![];
        if !self.peek(&TokenEnum::RightParen) {
            params.extend(self.parse_party_params()?);
            self.expect(&TokenEnum::RightParen)?;
        } else {
            self.expect(&TokenEnum::RightParen)?;
        }

        // -> <ty>
        self.expect(&TokenEnum::Arrow)?;
        let (ty, _) = self.parse_type()?;

        // { ... }
        self.expect(&TokenEnum::LeftBrace)?;
        let body = self.parse_expr()?;
        let end = self.expect(&TokenEnum::RightBrace)?;

        let meta = join_meta(start, end);
        Ok(MainDef {
            ty,
            params,
            body,
            meta,
        })
    }

    fn parse_params(&mut self) -> Result<Vec<ParamDef>, ()> {
        let mut params = vec![self.parse_param()?];
        while let Some(_) = self.next_matches(&TokenEnum::Comma) {
            params.push(self.parse_param()?);
        }
        Ok(params)
    }

    fn parse_param(&mut self) -> Result<ParamDef, ()> {
        // <param>: <type>
        let (param_name, _) = self.expect_identifier()?;
        self.expect(&TokenEnum::Colon)?;
        let (ty, _) = self.parse_type()?;
        Ok(ParamDef(param_name, ty))
    }

    fn parse_party_params(&mut self) -> Result<Vec<(Party, ParamDef)>, ()> {
        let mut params = vec![self.parse_party_param()?];
        while let Some(_) = self.next_matches(&TokenEnum::Comma) {
            params.push(self.parse_party_param()?);
        }
        Ok(params)
    }

    fn parse_party_param(&mut self) -> Result<(Party, ParamDef), ()> {
        // <param>: <party>::<type>
        let (param_name, _) = self.expect_identifier()?;
        self.expect(&TokenEnum::Colon)?;
        let (party, party_meta) = self.expect_identifier()?;
        let party = match party.as_str() {
            "A" => Party::A,
            "B" => Party::B,
            _ => {
                self.push_error(RustishParseErrorEnum::InvalidParty, party_meta);
                return Err(());
            }
        };
        self.expect(&TokenEnum::DoubleColon)?;
        let (ty, _) = self.parse_type()?;
        Ok((party, ParamDef(param_name, ty)))
    }

    fn parse_expr(&mut self) -> Result<Expr, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::KeywordLet) {
            // let <var> = <binding>; <body>
            let (var, _) = self.expect_identifier()?;
            self.expect(&TokenEnum::Eq)?;
            if let Ok(binding) = self.parse_expr() {
                let meta_end = self.expect(&TokenEnum::Semicolon)?;
                let body = self.parse_expr()?;
                let meta = join_meta(meta, meta_end);
                Ok(Expr(
                    ExprEnum::Let(var, Box::new(binding), Box::new(body)),
                    meta,
                ))
            } else {
                self.consume_until_one_of(&[TokenEnum::Semicolon]);
                self.tokens.next();
                self.parse_expr()?;
                Err(())
            }
        } else if let Some(meta) = self.next_matches(&TokenEnum::KeywordIf) {
            // if <cond> { <then> } else { <else> }
            let cond_expr = self.parse_expr()?;
            self.expect(&TokenEnum::LeftBrace)?;

            if let Ok(then_expr) = self.parse_expr() {
                self.expect(&TokenEnum::RightBrace)?;
                self.expect(&TokenEnum::KeywordElse)?;
                self.expect(&TokenEnum::LeftBrace)?;

                let else_expr = self.parse_expr()?;
                let meta_end = self.expect(&TokenEnum::RightBrace)?;
                let meta = join_meta(meta, meta_end);
                Ok(Expr(
                    ExprEnum::If(
                        Box::new(cond_expr),
                        Box::new(then_expr),
                        Box::new(else_expr),
                    ),
                    meta,
                ))
            } else {
                self.consume_until_one_of(&[TokenEnum::RightBrace]);
                self.expect(&TokenEnum::RightBrace)?;
                self.expect(&TokenEnum::KeywordElse)?;
                self.expect(&TokenEnum::LeftBrace)?;

                let _else_expr = self.parse_expr()?;
                self.expect(&TokenEnum::RightBrace)?;

                return Err(());
            }
        } else if let Some(meta) = self.next_matches(&TokenEnum::KeywordMatch) {
            // match <match_expr> { <clause> * }
            let match_expr = self.parse_expr()?;
            self.expect(&TokenEnum::LeftBrace)?;

            let mut has_failed = false;
            let mut clauses = vec![];
            if let Ok(clause) = self.parse_match_clause() {
                clauses.push(clause);
            } else {
                has_failed = true;
                self.consume_until_one_of(&[TokenEnum::Comma, TokenEnum::RightBrace]);
            }
            while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                if !self.peek(&TokenEnum::RightBrace) {
                    if let Ok(clause) = self.parse_match_clause() {
                        clauses.push(clause);
                    } else {
                        has_failed = true;
                        self.consume_until_one_of(&[TokenEnum::Comma, TokenEnum::RightBrace]);
                    }
                }
            }
            if has_failed {
                return Err(());
            }

            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            Ok(Expr(ExprEnum::Match(Box::new(match_expr), clauses), meta))
        } else {
            self.parse_equality()
        }
    }

    fn parse_match_clause(&mut self) -> Result<(Pattern, Expr), ()> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenEnum::FatArrow)?;
        let expr = self.parse_expr()?;
        Ok((pattern, expr))
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ()> {
        if let Some(Token(token_enum, meta)) = self.tokens.peek() {
            match token_enum {
                TokenEnum::Identifier(identifier) => {
                    let identifier = identifier.clone();
                    let meta = *meta;
                    self.tokens.next();
                    match identifier.as_str() {
                        "true" => return Ok(Pattern(PatternEnum::True, meta)),
                        "false" => return Ok(Pattern(PatternEnum::False, meta)),
                        _ => {}
                    }
                    if let Some(_) = self.next_matches(&TokenEnum::DoubleColon) {
                        let (variant_name, variant_meta) = self.expect_identifier()?;
                        if self.peek(&TokenEnum::LeftParen) {
                            let meta_start = self.expect(&TokenEnum::LeftParen)?;
                            let mut fields = vec![];
                            if !self.peek(&TokenEnum::RightParen) {
                                fields.push(self.parse_pattern()?);
                                while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                                    fields.push(self.parse_pattern()?);
                                }
                            }
                            let meta_end = self.expect(&TokenEnum::RightParen)?;
                            let meta = join_meta(meta_start, meta_end);
                            Ok(Pattern(PatternEnum::EnumTuple(variant_name, fields), meta))
                        } else {
                            let meta = join_meta(meta, variant_meta);
                            Ok(Pattern(PatternEnum::EnumUnit(variant_name), meta))
                        }
                    } else {
                        // TODO: need to distinguish between identifier and unit enums
                        Ok(Pattern(PatternEnum::Identifier(identifier), meta))
                    }
                }
                TokenEnum::UnsignedNum(n) => {
                    let n = *n;
                    let meta = *meta;
                    self.tokens.next();
                    if let Some(Token(TokenEnum::Dot, _)) = self.tokens.peek() {
                        self.tokens.next();
                        self.expect(&TokenEnum::Dot)?;
                        if let Some(Token(TokenEnum::UnsignedNum(range_end), meta_end)) =
                            self.tokens.peek()
                        {
                            let range_end = *range_end;
                            let meta_end = *meta_end;
                            self.tokens.next();

                            let meta = join_meta(meta, meta_end);
                            Ok(Pattern(
                                PatternEnum::UnsignedInclusiveRange(n, range_end - 1),
                                meta,
                            ))
                        } else {
                            self.push_error_for_next(RustishParseErrorEnum::InvalidRangeExpr);
                            return Err(());
                        }
                    } else {
                        Ok(Pattern(PatternEnum::NumUnsigned(n), meta))
                    }
                }
                TokenEnum::SignedNum(n) => {
                    let n = *n;
                    let meta = *meta;
                    self.tokens.next();
                    if let Some(Token(TokenEnum::Dot, _)) = self.tokens.peek() {
                        self.tokens.next();
                        self.expect(&TokenEnum::Dot)?;
                        if let Some(Token(TokenEnum::UnsignedNum(range_end), meta_end)) =
                            self.tokens.peek()
                        {
                            let range_end = *range_end;
                            let meta_end = *meta_end;
                            self.tokens.next();

                            let meta = join_meta(meta, meta_end);
                            Ok(Pattern(
                                PatternEnum::SignedInclusiveRange(n, range_end as i128 - 1),
                                meta,
                            ))
                        } else if let Some(Token(TokenEnum::SignedNum(range_end), meta_end)) =
                            self.tokens.peek()
                        {
                            let range_end = *range_end;
                            let meta_end = *meta_end;
                            self.tokens.next();

                            let meta = join_meta(meta, meta_end);
                            Ok(Pattern(
                                PatternEnum::SignedInclusiveRange(n, range_end - 1),
                                meta,
                            ))
                        } else {
                            self.push_error_for_next(RustishParseErrorEnum::InvalidRangeExpr);
                            return Err(());
                        }
                    } else {
                        Ok(Pattern(PatternEnum::NumSigned(n), meta))
                    }
                }
                TokenEnum::LeftParen => {
                    let meta_start = self.expect(&TokenEnum::LeftParen)?;
                    let mut fields = vec![];
                    if !self.peek(&TokenEnum::RightParen) {
                        fields.push(self.parse_pattern()?);
                        while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                            fields.push(self.parse_pattern()?);
                        }
                    }
                    let meta_end = self.expect(&TokenEnum::RightParen)?;
                    let meta = join_meta(meta_start, meta_end);
                    Ok(Pattern(PatternEnum::Tuple(fields), meta))
                }
                _ => {
                    self.push_error_for_next(RustishParseErrorEnum::InvalidPattern);
                    self.consume_until_one_of(&[TokenEnum::FatArrow]);
                    Err(())
                }
            }
        } else {
            self.push_error_for_next(RustishParseErrorEnum::InvalidPattern);
            Err(())
        }
    }

    fn parse_equality(&mut self) -> Result<Expr, ()> {
        // ==, !=
        let ops = vec![TokenEnum::DoubleEq, TokenEnum::BangEq];
        let mut x = self.parse_comparison()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_comparison()?;
            let meta = join_expr_meta(&x, &y);
            let op = match token {
                TokenEnum::DoubleEq => Op::Eq,
                TokenEnum::BangEq => Op::NotEq,
                _ => unreachable!(),
            };
            x = Expr(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ()> {
        // >, <
        let ops = vec![TokenEnum::LessThan, TokenEnum::GreaterThan];
        let mut x = self.parse_logical_or()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_logical_or()?;
            let meta = join_expr_meta(&x, &y);
            let op = match token {
                TokenEnum::LessThan => Op::LessThan,
                TokenEnum::GreaterThan => Op::GreaterThan,
                _ => unreachable!(),
            };
            x = Expr(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_logical_or(&mut self) -> Result<Expr, ()> {
        // |
        let mut x = self.parse_logical_xor()?;
        while let Some(_) = self.next_matches(&TokenEnum::Bar) {
            let y = self.parse_logical_xor()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitOr, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_logical_xor(&mut self) -> Result<Expr, ()> {
        // ^
        let mut x = self.parse_logical_and()?;
        while let Some(_) = self.next_matches(&TokenEnum::Caret) {
            let y = self.parse_logical_and()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitXor, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_logical_and(&mut self) -> Result<Expr, ()> {
        // &
        let mut x = self.parse_shift()?;
        while let Some(_) = self.next_matches(&TokenEnum::Ampersand) {
            let y = self.parse_shift()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitAnd, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_shift(&mut self) -> Result<Expr, ()> {
        // <<, >>
        let ops = vec![TokenEnum::DoubleLessThan, TokenEnum::DoubleGreaterThan];
        let mut x = self.parse_term()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_term()?;
            let meta = join_expr_meta(&x, &y);
            let op = match token {
                TokenEnum::DoubleLessThan => Op::ShiftLeft,
                TokenEnum::DoubleGreaterThan => Op::ShiftRight,
                _ => unreachable!(),
            };
            x = Expr(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_term(&mut self) -> Result<Expr, ()> {
        // +, -
        let ops = vec![TokenEnum::Plus, TokenEnum::Minus];
        let mut x = self.parse_factor()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_factor()?;
            let meta = join_expr_meta(&x, &y);
            let op = match token {
                TokenEnum::Plus => Op::Add,
                TokenEnum::Minus => Op::Sub,
                _ => unreachable!(),
            };
            x = Expr(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_factor(&mut self) -> Result<Expr, ()> {
        // *, /, %
        let ops = vec![TokenEnum::Star, TokenEnum::Slash, TokenEnum::Percent];
        let mut x = self.parse_cast()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_cast()?;
            let meta = join_expr_meta(&x, &y);
            let op = match token {
                TokenEnum::Star => Op::Mul,
                TokenEnum::Percent => Op::Mod,
                TokenEnum::Slash => Op::Div,
                _ => unreachable!(),
            };
            x = Expr(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_cast(&mut self) -> Result<Expr, ()> {
        let mut x = self.parse_unary()?;
        while let Some(_) = self.next_matches(&TokenEnum::KeywordAs) {
            let (ty, ty_meta) = self.parse_type()?;
            let meta = join_meta(x.1, ty_meta);
            x = Expr(ExprEnum::Cast(ty, Box::new(x)), meta)
        }
        Ok(x)
    }

    fn parse_unary(&mut self) -> Result<Expr, ()> {
        // -, !
        if let Some(meta) = self.next_matches(&TokenEnum::Bang) {
            let primary = self.parse_primary()?;
            let Expr(_, expr_meta) = primary;
            let meta = join_meta(meta, expr_meta);
            Ok(Expr(
                ExprEnum::UnaryOp(UnaryOp::Not, Box::new(primary)),
                meta,
            ))
        } else if let Some(meta) = self.next_matches(&TokenEnum::Minus) {
            let primary = self.parse_primary()?;
            let Expr(_, expr_meta) = primary;
            let meta = join_meta(meta, expr_meta);
            Ok(Expr(
                ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(primary)),
                meta,
            ))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, ()> {
        let mut expr = if let Some(Token(token_enum, meta)) = self.tokens.next() {
            match token_enum {
                TokenEnum::Identifier(identifier) => match identifier.as_str() {
                    "true" => Expr(ExprEnum::True, meta),
                    "false" => Expr(ExprEnum::False, meta),
                    _ => {
                        if let Some(_) = self.next_matches(&TokenEnum::DoubleColon) {
                            let (variant_name, variant_meta) = self.expect_identifier()?;
                            let variant = if let Some(_) = self.next_matches(&TokenEnum::LeftParen)
                            {
                                let mut fields = vec![];
                                if !self.peek(&TokenEnum::RightParen) {
                                    fields.push(self.parse_expr()?);
                                    while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                                        fields.push(self.parse_expr()?);
                                    }
                                }
                                let end = self.expect(&TokenEnum::RightParen)?;
                                let variant_meta = join_meta(variant_meta, end);
                                VariantExpr(
                                    variant_name,
                                    VariantExprEnum::Tuple(fields),
                                    variant_meta,
                                )
                            } else {
                                VariantExpr(variant_name, VariantExprEnum::Unit, variant_meta)
                            };
                            Expr(ExprEnum::EnumLiteral(identifier, Box::new(variant)), meta)
                        } else if let Some(_) = self.next_matches(&TokenEnum::LeftParen) {
                            let mut args = vec![];
                            if !self.peek(&TokenEnum::RightParen) {
                                args.push(self.parse_expr()?);
                                while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                                    args.push(self.parse_expr()?);
                                }
                            }
                            let end = self.expect(&TokenEnum::RightParen)?;
                            let meta = join_meta(meta, end);
                            Expr(ExprEnum::FnCall(identifier, args), meta)
                        } else {
                            Expr(ExprEnum::Identifier(identifier), meta)
                        }
                    }
                },
                TokenEnum::UnsignedNum(n) => {
                    if let Some(Token(TokenEnum::Dot, _)) = self.tokens.peek() {
                        self.tokens.next();
                        self.expect(&TokenEnum::Dot)?;
                        if let Some(Token(TokenEnum::UnsignedNum(range_end), meta_end)) =
                            self.tokens.peek()
                        {
                            let range_end = *range_end;
                            let meta_end = *meta_end;
                            self.tokens.next();
                            if n < usize::MAX as u128 && range_end < usize::MAX as u128 {
                                let meta = join_meta(meta, meta_end);
                                Expr(ExprEnum::Range(n as usize, range_end as usize), meta)
                            } else {
                                self.push_error(RustishParseErrorEnum::InvalidRangeExpr, meta_end);
                                return Err(());
                            }
                        } else {
                            self.push_error_for_next(RustishParseErrorEnum::InvalidRangeExpr);
                            return Err(());
                        }
                    } else {
                        Expr(ExprEnum::NumUnsigned(n), meta)
                    }
                }
                TokenEnum::SignedNum(n) => Expr(ExprEnum::NumSigned(n), meta),
                TokenEnum::LeftParen => {
                    if !self.peek(&TokenEnum::RightParen) {
                        let expr = self.parse_expr()?;
                        if self.peek(&TokenEnum::Comma) {
                            let mut fields = vec![expr];
                            while let Some(_) = self.next_matches(&TokenEnum::Comma) {
                                fields.push(self.parse_expr()?);
                            }
                            let tuple_end = self.expect(&TokenEnum::RightParen)?;
                            let meta = join_meta(meta, tuple_end);
                            Expr(ExprEnum::TupleLiteral(fields), meta)
                        } else {
                            self.expect(&TokenEnum::RightParen)?;
                            expr
                        }
                    } else {
                        Expr(ExprEnum::TupleLiteral(vec![]), meta)
                    }
                }
                TokenEnum::LeftBracket => {
                    let elem = self.parse_expr()?;
                    self.expect(&TokenEnum::Semicolon)?;
                    let size = if let Some(Token(TokenEnum::UnsignedNum(n), meta)) =
                        self.tokens.peek()
                    {
                        let n = *n;
                        let meta = *meta;
                        self.tokens.next();
                        if n <= usize::MAX as u128 {
                            n as usize
                        } else {
                            self.push_error(RustishParseErrorEnum::InvalidArraySize, meta);
                            return Err(());
                        }
                    } else {
                        self.push_error_for_next(RustishParseErrorEnum::ExpectedConstantArraySize);
                        return Err(());
                    };
                    self.expect(&TokenEnum::RightBracket)?;
                    Expr(ExprEnum::ArrayLiteral(Box::new(elem), size), meta)
                }
                _ => {
                    self.push_error(RustishParseErrorEnum::ExpectedExpr, meta);
                    return Err(());
                }
            }
        } else {
            self.push_error_for_next(RustishParseErrorEnum::ExpectedExpr);
            return Err(());
        };
        while let Some(_) = self.next_matches(&TokenEnum::LeftBracket) {
            let index = self.parse_expr()?;
            if let Some(_) = self.next_matches(&TokenEnum::Arrow) {
                let replacement = self.parse_expr()?;
                let end = self.expect(&TokenEnum::RightBracket)?;
                let meta = join_meta(expr.1, end);
                expr = Expr(
                    ExprEnum::ArrayAssignment(
                        Box::new(expr),
                        Box::new(index),
                        Box::new(replacement),
                    ),
                    meta,
                );
            } else {
                let end = self.expect(&TokenEnum::RightBracket)?;
                let meta = join_meta(expr.1, end);
                expr = Expr(ExprEnum::ArrayAccess(Box::new(expr), Box::new(index)), meta);
            }
        }
        while let Some(_) = self.next_matches(&TokenEnum::Dot) {
            let peeked = self.tokens.peek();
            if let Some(Token(TokenEnum::Identifier(_), _)) = peeked {
                expr = self.parse_method_call(expr)?;
            } else if let Some(Token(TokenEnum::UnsignedNum(i), meta_index)) = peeked {
                let i = *i;
                let meta_index = *meta_index;
                if i <= usize::MAX as u128 {
                    self.tokens.next();
                    let meta = join_meta(expr.1, meta_index);
                    expr = Expr(ExprEnum::TupleAccess(Box::new(expr), i as usize), meta)
                } else {
                    self.push_error_for_next(RustishParseErrorEnum::InvalidTupleIndexSize);
                }
            } else {
                self.push_error_for_next(RustishParseErrorEnum::ExpectedMethodCallOrFieldAccess);
                return Err(());
            }
        }
        Ok(expr)
    }

    fn parse_method_call(&mut self, recv: Expr) -> Result<Expr, ()> {
        let (method_name, call_start) = self.expect_identifier()?;
        match method_name.as_str() {
            "map" => {
                // .map(|<param>: <type>| -> <ret_ty> { <body> })
                self.expect(&TokenEnum::LeftParen)?;

                let closure_start = self.expect(&TokenEnum::Bar)?;
                let (param_name, _) = self.expect_identifier()?;
                self.expect(&TokenEnum::Colon)?;
                let (param_ty, _) = self.parse_type()?;
                self.expect(&TokenEnum::Bar)?;
                self.expect(&TokenEnum::Arrow)?;
                let (ret_ty, _) = self.parse_type()?;
                self.expect(&TokenEnum::LeftBrace)?;
                let body = self.parse_expr()?;
                let closure_end = self.expect(&TokenEnum::RightBrace)?;

                let closure_meta = join_meta(closure_start, closure_end);
                let closure = Closure {
                    ty: ret_ty,
                    params: vec![ParamDef(param_name, param_ty)],
                    body,
                    meta: closure_meta,
                };

                let call_end = self.expect(&TokenEnum::RightParen)?;
                let meta = join_meta(call_start, call_end);
                Ok(Expr(ExprEnum::Map(Box::new(recv), Box::new(closure)), meta))
            }
            "fold" => {
                // .fold(<init>, |<param1>: <type1>, <param1>: <type1>| -> <ret_ty> { <body> })
                self.expect(&TokenEnum::LeftParen)?;

                let init = self.parse_expr()?;
                self.expect(&TokenEnum::Comma)?;

                let closure_start = self.expect(&TokenEnum::Bar)?;

                let (param1_name, _) = self.expect_identifier()?;
                self.expect(&TokenEnum::Colon)?;
                let (param1_ty, _) = self.parse_type()?;

                self.expect(&TokenEnum::Comma)?;

                let (param2_name, _) = self.expect_identifier()?;
                self.expect(&TokenEnum::Colon)?;
                let (param2_ty, _) = self.parse_type()?;

                self.expect(&TokenEnum::Bar)?;
                self.expect(&TokenEnum::Arrow)?;
                let (ret_ty, _) = self.parse_type()?;
                self.expect(&TokenEnum::LeftBrace)?;
                let body = self.parse_expr()?;
                let closure_end = self.expect(&TokenEnum::RightBrace)?;

                let closure_meta = join_meta(closure_start, closure_end);
                let closure = Closure {
                    ty: ret_ty,
                    params: vec![
                        ParamDef(param1_name, param1_ty),
                        ParamDef(param2_name, param2_ty),
                    ],
                    body,
                    meta: closure_meta,
                };

                let call_end = self.expect(&TokenEnum::RightParen)?;
                let meta = join_meta(call_start, call_end);
                Ok(Expr(
                    ExprEnum::Fold(Box::new(recv), Box::new(init), Box::new(closure)),
                    meta,
                ))
            }
            _ => {
                self.push_error(RustishParseErrorEnum::InvalidMethodName, call_start);
                Err(())
            }
        }
    }

    fn parse_type(&mut self) -> Result<(Type, MetaInfo), ()> {
        let (ty, meta) = self.expect_identifier()?;
        let ty = match ty.as_str() {
            "bool" => Type::Bool,
            "usize" => Type::Usize,
            "u8" => Type::U8,
            "u16" => Type::U16,
            "u32" => Type::U32,
            "u64" => Type::U64,
            "u128" => Type::U128,
            "i8" => Type::I8,
            "i16" => Type::I16,
            "i32" => Type::I32,
            "i64" => Type::I64,
            "i128" => Type::I128,
            _ => {
                self.push_error(RustishParseErrorEnum::ExpectedType, meta);
                return Err(());
            }
        };
        Ok((ty, meta))
    }

    fn expect_identifier(&mut self) -> Result<(String, MetaInfo), ()> {
        if let Some(identifier) = self.next_matches_identifier() {
            Ok(identifier)
        } else {
            self.push_error_for_next(RustishParseErrorEnum::ExpectedIdentifier);
            Err(())
        }
    }

    fn expect(&mut self, t: &TokenEnum) -> Result<MetaInfo, ()> {
        if let Some(Token(next_token, meta)) = self.tokens.peek() {
            if next_token == t {
                let meta = *meta;
                self.tokens.next();
                return Ok(meta);
            }
        }
        self.push_error_for_next(RustishParseErrorEnum::UnexpectedToken);
        Err(())
    }

    fn consume_until_one_of(&mut self, options: &[TokenEnum]) {
        while let Some(Token(token_enum, _)) = self.tokens.peek() {
            for option in options {
                if option == token_enum {
                    return;
                }
            }
            self.tokens.next();
        }
    }

    fn next_matches_one_of(&mut self, options: &[TokenEnum]) -> Option<(TokenEnum, MetaInfo)> {
        for option in options {
            if let Some(meta) = self.next_matches(option) {
                return Some((option.clone(), meta));
            }
        }
        None
    }

    fn next_matches_identifier(&mut self) -> Option<(String, MetaInfo)> {
        match self.tokens.peek() {
            Some(Token(TokenEnum::Identifier(_), _)) => match self.tokens.next() {
                Some(Token(TokenEnum::Identifier(identifier), meta)) => Some((identifier, meta)),
                _ => unreachable!(),
            },
            _ => None,
        }
    }

    fn next_matches(&mut self, t: &TokenEnum) -> Option<MetaInfo> {
        if self.peek(t) {
            if let Some(Token(_, meta)) = self.tokens.next() {
                return Some(meta);
            }
        }
        None
    }

    fn peek(&mut self, t: &TokenEnum) -> bool {
        if let Some(Token(next_token, _)) = self.tokens.peek() {
            return next_token == t;
        }
        false
    }

    fn push_error_for_next(&mut self, err: RustishParseErrorEnum) {
        let meta = self
            .tokens
            .next()
            .map(|Token(_, meta)| meta)
            .unwrap_or_else(|| MetaInfo {
                start: (0, 0),
                end: (0, 0),
            });
        self.errors.push(RustishParseError(err, meta));
    }

    fn push_error(&mut self, err: RustishParseErrorEnum, meta: MetaInfo) {
        self.errors.push(RustishParseError(err, meta));
        self.tokens.next();
    }
}

fn join_expr_meta(x: &Expr, y: &Expr) -> MetaInfo {
    join_meta(x.1, y.1)
}

fn join_meta(x: MetaInfo, y: MetaInfo) -> MetaInfo {
    MetaInfo {
        start: x.start,
        end: y.end,
    }
}

pub fn parse(prg: &str) -> Result<Program, ParseError> {
    let sexprs = parse_into_sexprs(prg)?;
    let ast = parse_into_ast(sexprs)?;
    Ok(ast)
}

#[derive(Debug, Clone)]
struct Sexpr(SexprEnum, MetaInfo);

#[derive(Debug, Clone)]
enum SexprEnum {
    True,
    False,
    NumUnsigned(u128),
    NumSigned(i128),
    List(Vec<Sexpr>),
    Identifier(String),
}

#[derive(Debug, Clone)]
enum ParsedDef {
    Enum(EnumDef),
    Fn(FnDef),
}

fn parse_into_ast(mut sexprs: Vec<Sexpr>) -> Result<Program, ParseError> {
    let main = sexprs.pop().unwrap();
    let mut enum_defs = Vec::new();
    let mut fn_defs = Vec::new();
    for sexpr in sexprs.into_iter() {
        let parsed = parse_def(sexpr)?;
        match parsed {
            ParsedDef::Enum(def) => enum_defs.push(def),
            ParsedDef::Fn(def) => fn_defs.push(def),
        }
    }
    let main = parse_main_def(main)?;
    Ok(Program {
        enum_defs,
        fn_defs,
        main,
    })
}

fn parse_def(sexpr: Sexpr) -> Result<ParsedDef, ParseError> {
    let Sexpr(sexpr_enum, meta) = sexpr.clone();
    match sexpr_enum {
        SexprEnum::List(sexprs) => {
            if sexprs.is_empty() {
                return Err(ParseError(ParseErrorEnum::InvalidDef, meta));
            }
            let (keyword, meta) = expect_identifier(sexprs[0].clone())?;
            match keyword.as_str() {
                "enum" => Ok(ParsedDef::Enum(parse_enum_def(sexpr)?)),
                "fn" => Ok(ParsedDef::Fn(parse_fn_def(sexpr)?)),
                _ => Err(ParseError(ParseErrorEnum::InvalidDef, meta)),
            }
        }
        _ => Err(ParseError(ParseErrorEnum::InvalidDef, meta)),
    }
}

fn parse_enum_def(sexpr: Sexpr) -> Result<EnumDef, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    if let SexprEnum::List(sexprs) = sexpr {
        let mut sexprs = sexprs.into_iter();
        if let (Some(keyword_fn), Some(identifier)) = (sexprs.next(), sexprs.next()) {
            expect_keyword(keyword_fn, "enum")?;
            let (identifier, _) = expect_identifier(identifier)?;
            let mut variants = Vec::new();
            while let Some(variant) = sexprs.next() {
                let Sexpr(variant, meta) = variant;
                if let SexprEnum::List(variant) = variant {
                    if variant.len() < 2 {
                        return Err(ParseError(ParseErrorEnum::InvalidEnumDef, meta));
                    }
                    let (variant_type, meta) = expect_identifier(variant[0].clone())?;
                    let (identifier, _) = expect_identifier(variant[1].clone())?;
                    let variant = match variant_type.as_str() {
                        "unit-variant" => Variant::Unit(identifier),
                        "tuple-variant" => {
                            let mut types = Vec::with_capacity(variant.len() - 2);
                            for ty in variant[2..].iter() {
                                let (ty, _) = expect_type(ty.clone())?;
                                types.push(ty);
                            }
                            Variant::Tuple(identifier, types)
                        }
                        _ => return Err(ParseError(ParseErrorEnum::InvalidEnumDef, meta)),
                    };
                    variants.push(variant);
                } else {
                    return Err(ParseError(ParseErrorEnum::InvalidEnumDef, meta));
                }
            }
            Ok(EnumDef {
                identifier,
                variants,
                meta,
            })
        } else {
            return Err(ParseError(ParseErrorEnum::InvalidEnumDef, meta));
        }
    } else {
        Err(ParseError(ParseErrorEnum::InvalidEnumDef, meta))
    }
}

fn parse_closure_def(sexpr: Sexpr) -> Result<Closure, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    match sexpr {
        SexprEnum::List(mut sexprs) => {
            let body = parse_expr(sexprs.pop().unwrap())?;
            let mut sexprs = sexprs.into_iter();
            if let (Some(keyword_fn), Some(ty)) = (sexprs.next(), sexprs.next()) {
                expect_keyword(keyword_fn, "lambda")?;
                let (ty, _) = expect_type(ty)?;
                let mut params = Vec::new();
                while let Some(param_def) = sexprs.next() {
                    let (param_def, _) = expect_fixed_list(param_def, 3)?;
                    let mut param_def = param_def.into_iter();
                    expect_keyword(param_def.next().unwrap(), "param")?;
                    let (identifier, _) = expect_identifier(param_def.next().unwrap())?;
                    let (ty, _) = expect_type(param_def.next().unwrap())?;
                    params.push(ParamDef(identifier, ty));
                }
                Ok(Closure {
                    ty,
                    params,
                    body,
                    meta,
                })
            } else {
                return Err(ParseError(ParseErrorEnum::InvalidFnDef, meta));
            }
        }
        _ => Err(ParseError(ParseErrorEnum::InvalidFnDef, meta)),
    }
}

fn parse_fn_def(sexpr: Sexpr) -> Result<FnDef, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    match sexpr {
        SexprEnum::List(mut sexprs) => {
            let body = parse_expr(sexprs.pop().unwrap())?;
            let mut sexprs = sexprs.into_iter();
            if let (Some(keyword_fn), Some(identifier), Some(ty)) =
                (sexprs.next(), sexprs.next(), sexprs.next())
            {
                expect_keyword(keyword_fn, "fn")?;
                let (identifier, _) = expect_identifier(identifier)?;
                let (ty, _) = expect_type(ty)?;
                let mut params = Vec::new();
                while let Some(param_def) = sexprs.next() {
                    let (param_def, _) = expect_fixed_list(param_def, 3)?;
                    let mut param_def = param_def.into_iter();
                    expect_keyword(param_def.next().unwrap(), "param")?;
                    let (identifier, _) = expect_identifier(param_def.next().unwrap())?;
                    let (ty, _) = expect_type(param_def.next().unwrap())?;
                    params.push(ParamDef(identifier, ty));
                }
                Ok(FnDef {
                    identifier,
                    ty,
                    params,
                    body,
                    meta,
                })
            } else {
                return Err(ParseError(ParseErrorEnum::InvalidFnDef, meta));
            }
        }
        _ => Err(ParseError(ParseErrorEnum::InvalidFnDef, meta)),
    }
}

fn parse_main_def(sexpr: Sexpr) -> Result<MainDef, ParseError> {
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
                Ok(MainDef {
                    ty,
                    params,
                    body,
                    meta,
                })
            } else {
                return Err(ParseError(ParseErrorEnum::InvalidMainFnDef, meta));
            }
        }
        _ => Err(ParseError(ParseErrorEnum::InvalidMainFnDef, meta)),
    }
}

fn parse_expr(sexpr: Sexpr) -> Result<Expr, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    let expr = match sexpr {
        SexprEnum::True => ExprEnum::True,
        SexprEnum::False => ExprEnum::False,
        SexprEnum::NumUnsigned(n) => ExprEnum::NumUnsigned(n),
        SexprEnum::NumSigned(n) => ExprEnum::NumSigned(n),
        SexprEnum::Identifier(s) => ExprEnum::Identifier(s),
        SexprEnum::List(sexprs) => {
            let arity = sexprs.len() - 1;
            let mut sexprs = sexprs.into_iter();
            let (f, _meta) = expect_identifier(sexprs.next().unwrap())?;

            match f.as_str() {
                "-" | "!" if arity == 1 => {
                    let op = match f.as_str() {
                        "-" => UnaryOp::Neg,
                        "!" => UnaryOp::Not,
                        _ => unreachable!(),
                    };
                    let x = parse_expr(sexprs.next().unwrap())?;
                    ExprEnum::UnaryOp(op, Box::new(x))
                }
                "+" | "-" | "*" | "/" | "%" | "&" | "^" | "|" | ">" | "<" | "==" | "!=" | "<<"
                | ">>" => {
                    if arity == 2 {
                        let op = match f.as_str() {
                            "+" => Op::Add,
                            "-" => Op::Sub,
                            "*" => Op::Mul,
                            "/" => Op::Div,
                            "%" => Op::Mod,
                            "&" => Op::BitAnd,
                            "^" => Op::BitXor,
                            "|" => Op::BitOr,
                            ">" => Op::GreaterThan,
                            "<" => Op::LessThan,
                            "==" => Op::Eq,
                            "!=" => Op::NotEq,
                            "<<" => Op::ShiftLeft,
                            ">>" => Op::ShiftRight,
                            _ => unreachable!(),
                        };
                        let x = parse_expr(sexprs.next().unwrap())?;
                        let y = parse_expr(sexprs.next().unwrap())?;
                        ExprEnum::Op(op, Box::new(x), Box::new(y))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "let" => {
                    if arity == 3 {
                        let (identifier, _) = expect_identifier(sexprs.next().unwrap())?;
                        let binding = parse_expr(sexprs.next().unwrap())?;
                        let body = parse_expr(sexprs.next().unwrap())?;
                        ExprEnum::Let(identifier, Box::new(binding), Box::new(body))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "if" => {
                    if arity == 3 {
                        let condition = parse_expr(sexprs.next().unwrap())?;
                        let case_true = parse_expr(sexprs.next().unwrap())?;
                        let case_false = parse_expr(sexprs.next().unwrap())?;
                        ExprEnum::If(
                            Box::new(condition),
                            Box::new(case_true),
                            Box::new(case_false),
                        )
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "call" => {
                    if arity > 0 {
                        let (identifier, _) = expect_identifier(sexprs.next().unwrap())?;
                        let mut exprs = Vec::new();
                        while let Some(sexpr) = sexprs.next() {
                            exprs.push(parse_expr(sexpr)?);
                        }
                        ExprEnum::FnCall(identifier, exprs)
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "cast" => {
                    if arity == 2 {
                        let (ty, _) = expect_type(sexprs.next().unwrap())?;
                        let expr = parse_expr(sexprs.next().unwrap())?;
                        ExprEnum::Cast(ty, Box::new(expr))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "array" => {
                    if arity == 2 {
                        let value = parse_expr(sexprs.next().unwrap())?;
                        let (size, size_meta) = expect_unsigned_num(sexprs.next().unwrap())?;
                        if size <= usize::MAX as u128 {
                            ExprEnum::ArrayLiteral(Box::new(value), size as usize)
                        } else {
                            return Err(ParseError(
                                ParseErrorEnum::ArrayMaxSizeExceeded(size),
                                size_meta,
                            ));
                        }
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "array-get" => {
                    if arity == 2 {
                        let arr = parse_expr(sexprs.next().unwrap())?;
                        let index = parse_expr(sexprs.next().unwrap())?;
                        ExprEnum::ArrayAccess(Box::new(arr), Box::new(index))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "array-set" => {
                    if arity == 3 {
                        let arr = parse_expr(sexprs.next().unwrap())?;
                        let index = parse_expr(sexprs.next().unwrap())?;
                        let value = parse_expr(sexprs.next().unwrap())?;
                        ExprEnum::ArrayAssignment(Box::new(arr), Box::new(index), Box::new(value))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "fold" => {
                    if arity == 3 {
                        let arr = parse_expr(sexprs.next().unwrap())?;
                        let init_value = parse_expr(sexprs.next().unwrap())?;
                        let closure = parse_closure_def(sexprs.next().unwrap())?;
                        ExprEnum::Fold(Box::new(arr), Box::new(init_value), Box::new(closure))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "map" => {
                    if arity == 2 {
                        let arr = parse_expr(sexprs.next().unwrap())?;
                        let closure = parse_closure_def(sexprs.next().unwrap())?;
                        ExprEnum::Map(Box::new(arr), Box::new(closure))
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "range" => {
                    if arity == 2 {
                        let (from, from_meta) = expect_unsigned_num(sexprs.next().unwrap())?;
                        if from <= usize::MAX as u128 {
                            let (to, to_meta) = expect_unsigned_num(sexprs.next().unwrap())?;
                            if to <= usize::MAX as u128 {
                                ExprEnum::Range(from as usize, to as usize)
                            } else {
                                return Err(ParseError(
                                    ParseErrorEnum::ArrayMaxSizeExceeded(to),
                                    to_meta,
                                ));
                            }
                        } else {
                            return Err(ParseError(
                                ParseErrorEnum::ArrayMaxSizeExceeded(from),
                                from_meta,
                            ));
                        }
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "tuple" => {
                    let mut parsed = Vec::with_capacity(arity);
                    for sexpr in sexprs {
                        parsed.push(parse_expr(sexpr)?);
                    }
                    ExprEnum::TupleLiteral(parsed)
                }
                "tuple-get" => {
                    if arity == 2 {
                        let tuple = parse_expr(sexprs.next().unwrap())?;
                        let (size, size_meta) = expect_unsigned_num(sexprs.next().unwrap())?;
                        if size <= usize::MAX as u128 {
                            ExprEnum::TupleAccess(Box::new(tuple), size as usize)
                        } else {
                            return Err(ParseError(
                                ParseErrorEnum::TupleMaxSizeExceeded(size),
                                size_meta,
                            ));
                        }
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "enum" => {
                    if arity == 2 {
                        let (identifier, _) = expect_identifier(sexprs.next().unwrap())?;
                        if let Sexpr(SexprEnum::List(variant), meta) = sexprs.next().unwrap() {
                            if variant.len() < 2 {
                                return Err(ParseError(ParseErrorEnum::InvalidEnumVariant, meta));
                            } else {
                                let mut variant = variant.into_iter();
                                let (variant_type, _) = expect_identifier(variant.next().unwrap())?;
                                let (variant_identifier, _) =
                                    expect_identifier(variant.next().unwrap())?;
                                let mut values = Vec::new();
                                for v in variant {
                                    values.push(parse_expr(v)?);
                                }
                                let variant_expr = match variant_type.as_str() {
                                    "unit-variant" => {
                                        if values.is_empty() {
                                            VariantExpr(
                                                variant_identifier,
                                                VariantExprEnum::Unit,
                                                meta,
                                            )
                                        } else {
                                            return Err(ParseError(
                                                ParseErrorEnum::InvalidEnumVariant,
                                                meta,
                                            ));
                                        }
                                    }
                                    "tuple-variant" => VariantExpr(
                                        variant_identifier,
                                        VariantExprEnum::Tuple(values),
                                        meta,
                                    ),
                                    _ => {
                                        return Err(ParseError(
                                            ParseErrorEnum::InvalidEnumVariant,
                                            meta,
                                        ))
                                    }
                                };
                                ExprEnum::EnumLiteral(identifier, Box::new(variant_expr))
                            }
                        } else {
                            return Err(ParseError(ParseErrorEnum::InvalidEnumVariant, meta));
                        }
                    } else {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                }
                "match" => {
                    if arity < 2 {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                    let expr = parse_expr(sexprs.next().unwrap())?;
                    let mut clauses = Vec::new();
                    while let Some(clause) = sexprs.next() {
                        let (clause, _) = expect_fixed_list(clause, 3)?;
                        let mut clause = clause.into_iter();
                        expect_keyword(clause.next().unwrap(), "clause")?;
                        let pattern = parse_pattern(clause.next().unwrap())?;
                        let body = parse_expr(clause.next().unwrap())?;
                        clauses.push((pattern, body));
                    }
                    ExprEnum::Match(Box::new(expr), clauses)
                }
                _ => {
                    return Err(ParseError(ParseErrorEnum::InvalidExpr, meta));
                }
            }
        }
    };
    Ok(Expr(expr, meta))
}

fn parse_pattern(sexpr: Sexpr) -> Result<Pattern, ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    let pattern = match sexpr {
        SexprEnum::True => PatternEnum::True,
        SexprEnum::False => PatternEnum::False,
        SexprEnum::NumUnsigned(n) => PatternEnum::NumUnsigned(n),
        SexprEnum::NumSigned(n) => PatternEnum::NumSigned(n),
        SexprEnum::Identifier(s) => PatternEnum::Identifier(s),
        SexprEnum::List(sexprs) => {
            let arity = sexprs.len();
            if arity < 2 {
                return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
            }
            let mut pattern = sexprs.into_iter();
            let (pattern_kind, pattern_kind_meta) = expect_identifier(pattern.next().unwrap())?;
            match pattern_kind.as_str() {
                "range" => {
                    if arity != 3 {
                        return Err(ParseError(ParseErrorEnum::InvalidArity(arity), meta));
                    }
                    let Sexpr(min, _) = pattern.next().unwrap();
                    let Sexpr(max, _) = pattern.next().unwrap();
                    match (min, max) {
                        (SexprEnum::NumUnsigned(min), SexprEnum::NumUnsigned(max)) => {
                            PatternEnum::UnsignedInclusiveRange(min, max - 1)
                        }
                        (SexprEnum::NumSigned(min), SexprEnum::NumUnsigned(max))
                            if max <= i128::MAX as u128 + 1 =>
                        {
                            PatternEnum::SignedInclusiveRange(min, (max - 1) as i128)
                        }
                        (SexprEnum::NumSigned(min), SexprEnum::NumSigned(max)) => {
                            PatternEnum::SignedInclusiveRange(min, max - 1)
                        }
                        _ => return Err(ParseError(ParseErrorEnum::InvalidRangePattern, meta)),
                    }
                }
                "tuple" => {
                    let mut fields = Vec::new();
                    for field in pattern {
                        fields.push(parse_pattern(field)?);
                    }
                    PatternEnum::Tuple(fields)
                }
                "unit-variant" | "tuple-variant" => {
                    let (variant_identifier, _) = expect_identifier(pattern.next().unwrap())?;
                    let mut fields = Vec::new();
                    for field in pattern {
                        fields.push(parse_pattern(field)?);
                    }
                    match (pattern_kind.as_str(), fields.len()) {
                        ("unit-variant", 0) => PatternEnum::EnumUnit(variant_identifier),
                        ("unit-variant", _) => {
                            return Err(ParseError(ParseErrorEnum::InvalidEnumVariant, meta))
                        }
                        ("tuple-variant", _) => PatternEnum::EnumTuple(variant_identifier, fields),
                        _ => return Err(ParseError(ParseErrorEnum::InvalidEnumPattern, meta)),
                    }
                }
                _ => {
                    return Err(ParseError(
                        ParseErrorEnum::InvalidPattern,
                        pattern_kind_meta,
                    ))
                }
            }
        }
    };
    Ok(Pattern(pattern, meta))
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
                "usize" => Type::Usize,
                "u8" => Type::U8,
                "u16" => Type::U16,
                "u32" => Type::U32,
                "u64" => Type::U64,
                "u128" => Type::U128,
                "i8" => Type::I8,
                "i16" => Type::I16,
                "i32" => Type::I32,
                "i64" => Type::I64,
                "i128" => Type::I128,
                _ => return Err(ParseError(ParseErrorEnum::ExpectedType, meta)),
            };
            Ok((ty, meta))
        }
        Err(ParseError(_, meta)) => Err(ParseError(ParseErrorEnum::ExpectedType, meta)),
    }
}

fn expect_unsigned_num(sexpr: Sexpr) -> Result<(u128, MetaInfo), ParseError> {
    let Sexpr(sexpr, meta) = sexpr;
    match sexpr {
        SexprEnum::NumUnsigned(n) => Ok((n, meta)),
        _ => Err(ParseError(ParseErrorEnum::ExpectedIdentifier, meta)),
    }
}

fn parse_into_sexprs(prg: &str) -> Result<Vec<Sexpr>, ParseError> {
    let mut stack = vec![vec![]];
    let mut stack_meta_start = vec![(0, 0)];
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
                        } else if let Ok(n) = token.parse::<i128>() {
                            SexprEnum::NumSigned(n)
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
    if stack.len() == 1 {
        let sexprs = stack.pop().unwrap();
        Ok(sexprs)
    } else {
        Err(ParseError(ParseErrorEnum::UnclosedSexpr, meta))
    }
}
