use std::{collections::HashMap, iter::Peekable, vec::IntoIter};

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
    pub fn parse(self) -> Result<Program, Vec<ParseError>> {
        Parser::new(self.0).parse()
    }
}

struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    errors: Vec<ParseError>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: vec![],
        }
    }

    fn parse(mut self) -> Result<Program, Vec<ParseError>> {
        let top_level_keywords = [TokenEnum::KeywordFn];
        let mut enum_defs = HashMap::new();
        let mut fn_defs = HashMap::new();
        let mut main_fn_def = None;
        let mut has_main = false;
        while let Some(Token(token_enum, meta)) = self.tokens.next() {
            match token_enum {
                TokenEnum::KeywordEnum => {
                    if let Ok(enum_def) = self.parse_enum_def(meta) {
                        enum_defs.insert(enum_def.identifier.clone(), enum_def);
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
                        } else if let Ok(fn_def) = self.parse_fn_def(meta) {
                            fn_defs.insert(fn_def.identifier.clone(), fn_def);
                        } else {
                            self.consume_until_one_of(&top_level_keywords);
                        }
                    }
                }
                _ => {
                    self.push_error(ParseErrorEnum::InvalidTopLevelDef, meta);
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
                self.push_error(ParseErrorEnum::MissingMainFnDef, meta);
            }
            Err(self.errors)
        }
    }

    fn parse_enum_def(&mut self, start: MetaInfo) -> Result<EnumDef, ()> {
        // enum keyword was already consumed by the top-level parser

        let (identifier, _) = self.expect_identifier()?;

        self.expect(&TokenEnum::LeftBrace)?;

        let mut variants = vec![self.parse_variant()?];

        while self.next_matches(&TokenEnum::Comma).is_some() {
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
        if self.next_matches(&TokenEnum::LeftParen).is_some() {
            let mut fields = vec![];
            if let Some(Token(TokenEnum::Identifier(_), _)) = self.tokens.peek() {
                let (ty, _) = self.parse_type()?;
                fields.push(ty);
            }
            while self.next_matches(&TokenEnum::Comma).is_some() {
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
        }
        self.expect(&TokenEnum::RightParen)?;

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
        }
        self.expect(&TokenEnum::RightParen)?;

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
        while self.next_matches(&TokenEnum::Comma).is_some() {
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
        while self.next_matches(&TokenEnum::Comma).is_some() {
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
                self.push_error(ParseErrorEnum::InvalidParty, party_meta);
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

                Err(())
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
            while self.next_matches(&TokenEnum::Comma).is_some() {
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
                    if self.next_matches(&TokenEnum::DoubleColon).is_some() {
                        let (variant_name, variant_meta) = self.expect_identifier()?;
                        if self.peek(&TokenEnum::LeftParen) {
                            let meta_start = self.expect(&TokenEnum::LeftParen)?;
                            let mut fields = vec![];
                            if !self.peek(&TokenEnum::RightParen) {
                                fields.push(self.parse_pattern()?);
                                while self.next_matches(&TokenEnum::Comma).is_some() {
                                    fields.push(self.parse_pattern()?);
                                }
                            }
                            let meta_end = self.expect(&TokenEnum::RightParen)?;
                            let meta = join_meta(meta_start, meta_end);
                            Ok(Pattern(
                                PatternEnum::EnumTuple(identifier, variant_name, fields),
                                meta,
                            ))
                        } else {
                            let meta = join_meta(meta, variant_meta);
                            Ok(Pattern(
                                PatternEnum::EnumUnit(identifier, variant_name),
                                meta,
                            ))
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
                            self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                            Err(())
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
                            self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                            Err(())
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
                        while self.next_matches(&TokenEnum::Comma).is_some() {
                            fields.push(self.parse_pattern()?);
                        }
                    }
                    let meta_end = self.expect(&TokenEnum::RightParen)?;
                    let meta = join_meta(meta_start, meta_end);
                    Ok(Pattern(PatternEnum::Tuple(fields), meta))
                }
                _ => {
                    self.push_error_for_next(ParseErrorEnum::InvalidPattern);
                    self.consume_until_one_of(&[TokenEnum::FatArrow]);
                    Err(())
                }
            }
        } else {
            self.push_error_for_next(ParseErrorEnum::InvalidPattern);
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
        while self.next_matches(&TokenEnum::Bar).is_some() {
            let y = self.parse_logical_xor()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitOr, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_logical_xor(&mut self) -> Result<Expr, ()> {
        // ^
        let mut x = self.parse_logical_and()?;
        while self.next_matches(&TokenEnum::Caret).is_some() {
            let y = self.parse_logical_and()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitXor, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_logical_and(&mut self) -> Result<Expr, ()> {
        // &
        let mut x = self.parse_shift()?;
        while self.next_matches(&TokenEnum::Ampersand).is_some() {
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
        while self.next_matches(&TokenEnum::KeywordAs).is_some() {
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
                        if self.next_matches(&TokenEnum::DoubleColon).is_some() {
                            let (variant_name, variant_meta) = self.expect_identifier()?;
                            let variant = if self.next_matches(&TokenEnum::LeftParen).is_some() {
                                let mut fields = vec![];
                                if !self.peek(&TokenEnum::RightParen) {
                                    fields.push(self.parse_expr()?);
                                    while self.next_matches(&TokenEnum::Comma).is_some() {
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
                        } else if self.next_matches(&TokenEnum::LeftParen).is_some() {
                            let mut args = vec![];
                            if !self.peek(&TokenEnum::RightParen) {
                                args.push(self.parse_expr()?);
                                while self.next_matches(&TokenEnum::Comma).is_some() {
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
                                self.push_error(ParseErrorEnum::InvalidRangeExpr, meta_end);
                                return Err(());
                            }
                        } else {
                            self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
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
                            while self.next_matches(&TokenEnum::Comma).is_some() {
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
                    let size =
                        if let Some(Token(TokenEnum::UnsignedNum(n), meta)) = self.tokens.peek() {
                            let n = *n;
                            let meta = *meta;
                            self.tokens.next();
                            if n <= usize::MAX as u128 {
                                n as usize
                            } else {
                                self.push_error(ParseErrorEnum::InvalidArraySize, meta);
                                return Err(());
                            }
                        } else {
                            self.push_error_for_next(ParseErrorEnum::ExpectedConstantArraySize);
                            return Err(());
                        };
                    self.expect(&TokenEnum::RightBracket)?;
                    Expr(ExprEnum::ArrayLiteral(Box::new(elem), size), meta)
                }
                _ => {
                    self.push_error(ParseErrorEnum::ExpectedExpr, meta);
                    return Err(());
                }
            }
        } else {
            self.push_error_for_next(ParseErrorEnum::ExpectedExpr);
            return Err(());
        };
        while self.next_matches(&TokenEnum::LeftBracket).is_some() {
            let index = self.parse_expr()?;
            let end = self.expect(&TokenEnum::RightBracket)?;
            let meta = join_meta(expr.1, end);
            expr = Expr(ExprEnum::ArrayAccess(Box::new(expr), Box::new(index)), meta);
        }
        while self.next_matches(&TokenEnum::Dot).is_some() {
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
                    self.push_error_for_next(ParseErrorEnum::InvalidTupleIndexSize);
                }
            } else {
                self.push_error_for_next(ParseErrorEnum::ExpectedMethodCallOrFieldAccess);
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
            "update" => {
                // .update(<index>, <expr>)
                self.expect(&TokenEnum::LeftParen)?;

                let index = self.parse_expr()?;
                self.expect(&TokenEnum::Comma)?;

                let replacement = self.parse_expr()?;

                let end = self.expect(&TokenEnum::RightParen)?;
                let meta = join_meta(call_start, end);
                Ok(Expr(
                    ExprEnum::ArrayAssignment(
                        Box::new(recv),
                        Box::new(index),
                        Box::new(replacement),
                    ),
                    meta,
                ))
            }
            _ => {
                self.push_error(ParseErrorEnum::InvalidMethodName, call_start);
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
                self.push_error(ParseErrorEnum::ExpectedType, meta);
                return Err(());
            }
        };
        Ok((ty, meta))
    }

    fn expect_identifier(&mut self) -> Result<(String, MetaInfo), ()> {
        if let Some(identifier) = self.next_matches_identifier() {
            Ok(identifier)
        } else {
            self.push_error_for_next(ParseErrorEnum::ExpectedIdentifier);
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
        self.push_error_for_next(ParseErrorEnum::UnexpectedToken);
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

    fn push_error_for_next(&mut self, err: ParseErrorEnum) {
        let meta = self
            .tokens
            .next()
            .map(|Token(_, meta)| meta)
            .unwrap_or_else(|| MetaInfo {
                start: (0, 0),
                end: (0, 0),
            });
        self.errors.push(ParseError(err, meta));
    }

    fn push_error(&mut self, err: ParseErrorEnum, meta: MetaInfo) {
        self.errors.push(ParseError(err, meta));
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
