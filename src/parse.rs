//! Parses a stream of [`crate::scan::Tokens`] into an untyped [`crate::ast::Program`].

use std::{collections::HashMap, iter::Peekable, vec::IntoIter};

use crate::{
    ast::{
        Closure, EnumDef, Expr, ExprEnum, FnDef, Op, ParamDef, Pattern, PatternEnum, Program, Type,
        UnaryOp, Variant, VariantExpr, VariantExprEnum,
    },
    scan::Tokens,
    token::{MetaInfo, SignedNumType, Token, TokenEnum, UnsignedNumType},
};

/// An error found during parsing, with its location in the source code.
#[derive(Debug, Clone)]
pub struct ParseError(pub ParseErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]

/// The different kinds of errors found during parsing.
pub enum ParseErrorEnum {
    /// No `main` function exists in the source code.
    MissingMainFnDef,
    /// The top level definition is not a valid enum or function declaration.
    InvalidTopLevelDef,
    /// Arrays of the specified size are not supported.
    InvalidArraySize,
    /// Tuples of the specified size are not supported.
    InvalidTupleIndexSize,
    /// The method name is none of the supported (hardcoded) method names.
    InvalidMethodName,
    /// The min or max value of the range expression is invalid.
    InvalidRangeExpr,
    /// The pattern is not valid.
    InvalidPattern,
    /// The literal is not valid.
    InvalidLiteral,
    /// Expected a type, but found a non-type token.
    ExpectedType,
    /// Expected an expression, but found a non-expr token.
    ExpectedExpr,
    /// Expected an identifier, but found a non-identifier token.
    ExpectedIdentifier,
    /// Expected a method call or a field access.
    ExpectedMethodCallOrFieldAccess,
    /// Found an unexpected token.
    Expected(TokenEnum),
}

impl std::fmt::Display for ParseErrorEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseErrorEnum::MissingMainFnDef => f.write_str("Missing 'main' function definition"),
            ParseErrorEnum::InvalidTopLevelDef => {
                f.write_str("Not a valid function or enum definition")
            }
            ParseErrorEnum::InvalidArraySize => {
                let max = usize::MAX;
                f.write_fmt(format_args!(
                    "Invalid array size (must be a constant number <= {max})"
                ))
            }
            ParseErrorEnum::InvalidTupleIndexSize => f.write_str("Invalid tuple index"),
            ParseErrorEnum::InvalidMethodName => {
                f.write_str("Invalid method name (only .map, .fold and .update are supported)")
            }
            ParseErrorEnum::InvalidRangeExpr => f.write_str("Invalid range expression"),
            ParseErrorEnum::InvalidPattern => f.write_str("Invalid pattern"),
            ParseErrorEnum::InvalidLiteral => f.write_str("Invalid literal"),
            ParseErrorEnum::ExpectedType => f.write_str("Expected a type"),
            ParseErrorEnum::ExpectedExpr => f.write_str("Expected an expression"),
            ParseErrorEnum::ExpectedIdentifier => f.write_str("Expected an identifier"),
            ParseErrorEnum::ExpectedMethodCallOrFieldAccess => {
                f.write_str("Expected a method call or field access")
            }
            ParseErrorEnum::Expected(token) => f.write_fmt(format_args!("Expected '{token}'")),
        }
    }
}

impl Tokens {
    /// Parses the token stream as a program, returning either an untyped program or parse errors.
    pub fn parse(self) -> Result<Program, Vec<ParseError>> {
        Parser::new(self.0).parse()
    }

    pub(crate) fn parse_literal(self) -> Result<Expr, Vec<ParseError>> {
        let mut parser = Parser::new(self.0);
        if let Some(token) = parser.tokens.next() {
            parser.parse_literal(token, true).map_err(|_| parser.errors)
        } else {
            let e = ParseErrorEnum::InvalidLiteral;
            let meta = MetaInfo {
                start: (0, 0),
                end: (0, 0),
            };
            Err(vec![ParseError(e, meta)])
        }
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
                            if let Ok(main_def) = self.parse_fn_def(meta) {
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
            if self.errors.is_empty() {
                return Ok(Program {
                    enum_defs,
                    fn_defs,
                    main,
                });
            }
        }
        if !has_main {
            let meta = MetaInfo {
                start: (0, 0),
                end: (0, 0),
            };
            self.push_error(ParseErrorEnum::MissingMainFnDef, meta);
        }
        Err(self.errors)
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

    fn parse_params(&mut self) -> Result<Vec<ParamDef>, ()> {
        let mut params = vec![self.parse_param()?];
        while self.next_matches(&TokenEnum::Comma).is_some() {
            if self.peek(&TokenEnum::RightParen) {
                break;
            } else {
                params.push(self.parse_param()?);
            }
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

    fn parse_expr(&mut self) -> Result<Expr, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::LeftBrace) {
            // { ... }
            let expr = self.parse_expr()?;
            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            Ok(Expr(ExprEnum::LexicallyScopedBlock(Box::new(expr)), meta))
        } else if let Some(meta) = self.next_matches(&TokenEnum::KeywordLet) {
            // let <var> = <binding>; <body>
            let (var, _) = self.expect_identifier()?;
            self.expect(&TokenEnum::Eq)?;
            if let Ok(binding) = self.parse_expr() {
                self.expect(&TokenEnum::Semicolon)?;
                let body = self.parse_expr()?;
                let meta = join_meta(meta, body.1);
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
        } else {
            self.parse_short_circuiting_or()
        }
    }

    fn parse_short_circuiting_or(&mut self) -> Result<Expr, ()> {
        // ||
        let mut x = self.parse_short_circuiting_and()?;
        while self.next_matches(&TokenEnum::DoubleBar).is_some() {
            let y = self.parse_short_circuiting_and()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(
                ExprEnum::Op(Op::ShortCircuitOr, Box::new(x), Box::new(y)),
                meta,
            );
        }
        Ok(x)
    }

    fn parse_short_circuiting_and(&mut self) -> Result<Expr, ()> {
        // &&
        let mut x = self.parse_equality()?;
        while self.next_matches(&TokenEnum::DoubleAmpersand).is_some() {
            let y = self.parse_equality()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(
                ExprEnum::Op(Op::ShortCircuitAnd, Box::new(x), Box::new(y)),
                meta,
            );
        }
        Ok(x)
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
        let mut x = self.parse_or()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_or()?;
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

    fn parse_or(&mut self) -> Result<Expr, ()> {
        // |
        let mut x = self.parse_xor()?;
        while self.next_matches(&TokenEnum::Bar).is_some() {
            let y = self.parse_xor()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitOr, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_xor(&mut self) -> Result<Expr, ()> {
        // ^
        let mut x = self.parse_and()?;
        while self.next_matches(&TokenEnum::Caret).is_some() {
            let y = self.parse_and()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr(ExprEnum::Op(Op::BitXor, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_and(&mut self) -> Result<Expr, ()> {
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
        let mut x = self.parse_if_or_match()?;
        while self.next_matches(&TokenEnum::KeywordAs).is_some() {
            let (ty, ty_meta) = self.parse_type()?;
            let meta = join_meta(x.1, ty_meta);
            x = Expr(ExprEnum::Cast(ty, Box::new(x)), meta)
        }
        Ok(x)
    }

    fn parse_if_or_match(&mut self) -> Result<Expr, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::KeywordIf) {
            // if <cond> { <then> } else [if { <else-if> } else]* { <else> }
            let cond_expr = self.parse_expr()?;
            self.expect(&TokenEnum::LeftBrace)?;

            if let Ok(then_expr) = self.parse_expr() {
                self.expect(&TokenEnum::RightBrace)?;
                self.expect(&TokenEnum::KeywordElse)?;

                if self.peek(&TokenEnum::KeywordIf) {
                    let elseif_expr = self.parse_expr()?;
                    let meta = join_meta(meta, elseif_expr.1);
                    Ok(Expr(
                        ExprEnum::If(
                            Box::new(cond_expr),
                            Box::new(then_expr),
                            Box::new(elseif_expr),
                        ),
                        meta,
                    ))
                } else {
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
                }
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
            self.parse_unary()
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
                        Ok(Pattern(PatternEnum::Identifier(identifier), meta))
                    }
                }
                TokenEnum::UnsignedNum(n, type_suffix) => {
                    let n = *n;
                    let type_suffix = *type_suffix;
                    let meta = *meta;
                    self.tokens.next();
                    if let Some(Token(TokenEnum::Dot, _)) = self.tokens.peek() {
                        self.tokens.next();
                        self.expect(&TokenEnum::Dot)?;
                        if let Some(Token(
                            TokenEnum::UnsignedNum(range_end, type_suffix_end),
                            meta_end,
                        )) = self.tokens.peek()
                        {
                            if type_suffix == *type_suffix_end {
                                let range_end = *range_end;
                                let meta_end = *meta_end;
                                self.tokens.next();

                                let meta = join_meta(meta, meta_end);
                                Ok(Pattern(
                                    PatternEnum::UnsignedInclusiveRange(
                                        n,
                                        range_end - 1,
                                        type_suffix,
                                    ),
                                    meta,
                                ))
                            } else {
                                self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                                Err(())
                            }
                        } else {
                            self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                            Err(())
                        }
                    } else {
                        Ok(Pattern(PatternEnum::NumUnsigned(n, type_suffix), meta))
                    }
                }
                TokenEnum::SignedNum(n, type_suffix) => {
                    let n = *n;
                    let meta = *meta;
                    let type_suffix = *type_suffix;
                    self.tokens.next();
                    if let Some(Token(TokenEnum::Dot, _)) = self.tokens.peek() {
                        self.tokens.next();
                        self.expect(&TokenEnum::Dot)?;
                        if let Some(Token(
                            TokenEnum::SignedNum(range_end, type_suffix_end),
                            meta_end,
                        )) = self.tokens.peek()
                        {
                            if type_suffix == *type_suffix_end {
                                let range_end = *range_end;
                                let meta_end = *meta_end;
                                self.tokens.next();

                                let meta = join_meta(meta, meta_end);
                                Ok(Pattern(
                                    PatternEnum::SignedInclusiveRange(
                                        n,
                                        range_end - 1,
                                        type_suffix,
                                    ),
                                    meta,
                                ))
                            } else {
                                self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                                Err(())
                            }
                        } else {
                            self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                            Err(())
                        }
                    } else {
                        Ok(Pattern(PatternEnum::NumSigned(n, type_suffix), meta))
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

    fn parse_unary(&mut self) -> Result<Expr, ()> {
        // -, !
        if let Some(meta) = self.next_matches(&TokenEnum::Bang) {
            let unary = self.parse_unary()?;
            let Expr(_, expr_meta) = unary;
            let meta = join_meta(meta, expr_meta);
            Ok(Expr(ExprEnum::UnaryOp(UnaryOp::Not, Box::new(unary)), meta))
        } else if let Some(meta) = self.next_matches(&TokenEnum::Minus) {
            let unary = self.parse_unary()?;
            let Expr(_, expr_meta) = unary;
            let meta = join_meta(meta, expr_meta);
            Ok(Expr(ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(unary)), meta))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, ()> {
        let mut expr = if let Some(Token(token_enum, meta)) = self.tokens.next() {
            match &token_enum {
                TokenEnum::Identifier(identifier) => match identifier.as_str() {
                    "true" => self.parse_literal(Token(token_enum, meta), false)?,
                    "false" => self.parse_literal(Token(token_enum, meta), false)?,
                    _ => {
                        if self.peek(&TokenEnum::DoubleColon) {
                            self.parse_literal(Token(token_enum, meta), false)?
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
                            Expr(ExprEnum::FnCall(identifier.to_string(), args), meta)
                        } else {
                            Expr(ExprEnum::Identifier(identifier.to_string()), meta)
                        }
                    }
                },
                _ => self.parse_literal(Token(token_enum, meta), false)?,
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
            } else if let Some(Token(
                TokenEnum::UnsignedNum(i, Some(UnsignedNumType::Usize) | None),
                meta_index,
            )) = peeked
            {
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

    fn parse_literal_recusively(&mut self) -> Result<Expr, ()> {
        if let Some(token) = self.tokens.next() {
            self.parse_literal(token, true)
        } else {
            let meta = MetaInfo {
                start: (0, 0),
                end: (0, 0),
            };
            self.push_error(ParseErrorEnum::InvalidLiteral, meta);
            Err(())
        }
    }

    fn parse_literal(&mut self, token: Token, only_literal_children: bool) -> Result<Expr, ()> {
        let Token(token_enum, meta) = token;
        Ok(match token_enum {
            TokenEnum::Identifier(identifier) => match identifier.as_str() {
                "true" => Expr(ExprEnum::True, meta),
                "false" => Expr(ExprEnum::False, meta),
                _ => {
                    if self.next_matches(&TokenEnum::DoubleColon).is_some() {
                        let (variant_name, variant_meta) = self.expect_identifier()?;
                        let variant = if self.next_matches(&TokenEnum::LeftParen).is_some() {
                            let mut fields = vec![];
                            if !self.peek(&TokenEnum::RightParen) {
                                let child = if only_literal_children {
                                    self.parse_literal_recusively()?
                                } else {
                                    self.parse_expr()?
                                };
                                fields.push(child);
                                while self.next_matches(&TokenEnum::Comma).is_some() {
                                    let child = if only_literal_children {
                                        self.parse_literal_recusively()?
                                    } else {
                                        self.parse_expr()?
                                    };
                                    fields.push(child);
                                }
                            }
                            let end = self.expect(&TokenEnum::RightParen)?;
                            let variant_meta = join_meta(variant_meta, end);
                            VariantExpr(variant_name, VariantExprEnum::Tuple(fields), variant_meta)
                        } else {
                            VariantExpr(variant_name, VariantExprEnum::Unit, variant_meta)
                        };
                        Expr(ExprEnum::EnumLiteral(identifier, Box::new(variant)), meta)
                    } else {
                        self.push_error(ParseErrorEnum::InvalidLiteral, meta);
                        return Err(());
                    }
                }
            },
            TokenEnum::UnsignedNum(n, type_suffix) => {
                if let Some(Token(TokenEnum::Dot, _)) = self.tokens.peek() {
                    self.tokens.next();
                    self.expect(&TokenEnum::Dot)?;
                    if let Some(Token(TokenEnum::UnsignedNum(range_end, _), meta_end)) =
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
                    Expr(ExprEnum::NumUnsigned(n, type_suffix), meta)
                }
            }
            TokenEnum::SignedNum(n, type_suffix) => Expr(ExprEnum::NumSigned(n, type_suffix), meta),
            TokenEnum::LeftParen => {
                if !self.peek(&TokenEnum::RightParen) {
                    let expr = if only_literal_children {
                        self.parse_literal_recusively()?
                    } else {
                        self.parse_expr()?
                    };
                    if self.peek(&TokenEnum::Comma) {
                        let mut fields = vec![expr];
                        while self.next_matches(&TokenEnum::Comma).is_some() {
                            if self.peek(&TokenEnum::RightParen) {
                                break;
                            }
                            let child = if only_literal_children {
                                self.parse_literal_recusively()?
                            } else {
                                self.parse_expr()?
                            };
                            fields.push(child);
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
                let elem = if only_literal_children {
                    self.parse_literal_recusively()?
                } else {
                    self.parse_expr()?
                };
                if self.peek(&TokenEnum::Semicolon) {
                    self.expect(&TokenEnum::Semicolon)?;
                    let size = if let Some(Token(TokenEnum::UnsignedNum(n, None), meta)) =
                        self.tokens.peek()
                    {
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
                        self.push_error_for_next(ParseErrorEnum::InvalidArraySize);
                        return Err(());
                    };
                    let meta_end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(meta, meta_end);
                    Expr(ExprEnum::ArrayRepeatLiteral(Box::new(elem), size), meta)
                } else {
                    let mut elems = vec![elem];
                    while self.next_matches(&TokenEnum::Comma).is_some() {
                        let elem = if only_literal_children {
                            self.parse_literal_recusively()?
                        } else {
                            self.parse_expr()?
                        };
                        elems.push(elem);
                    }
                    let meta_end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(meta, meta_end);
                    Expr(ExprEnum::ArrayLiteral(elems), meta)
                }
            }
            _ => {
                self.push_error(ParseErrorEnum::ExpectedExpr, meta);
                return Err(());
            }
        })
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
        if let Some(meta) = self.next_matches(&TokenEnum::LeftParen) {
            let mut fields = vec![];
            if !self.peek(&TokenEnum::RightParen) {
                let (ty, _) = self.parse_type()?;
                fields.push(ty);
                while self.next_matches(&TokenEnum::Comma).is_some() {
                    let (ty, _) = self.parse_type()?;
                    fields.push(ty);
                }
            }
            let meta_end = self.expect(&TokenEnum::RightParen)?;
            let meta = join_meta(meta, meta_end);
            Ok((Type::Tuple(fields), meta))
        } else if let Some(meta) = self.next_matches(&TokenEnum::LeftBracket) {
            let (ty, _) = self.parse_type()?;
            self.expect(&TokenEnum::Semicolon)?;
            let size = if let Some(Token(TokenEnum::UnsignedNum(n, None), _)) = self.tokens.peek() {
                let n = *n;
                if n <= usize::MAX as u128 {
                    self.tokens.next();
                    n as usize
                } else {
                    self.push_error_for_next(ParseErrorEnum::InvalidArraySize);
                    return Err(());
                }
            } else {
                self.push_error_for_next(ParseErrorEnum::InvalidArraySize);
                return Err(());
            };
            let meta_end = self.expect(&TokenEnum::RightBracket)?;
            let meta = join_meta(meta, meta_end);
            Ok((Type::Array(Box::new(ty), size), meta))
        } else {
            let (ty, meta) = self.expect_identifier()?;
            let ty = match ty.as_str() {
                "bool" => Type::Bool,
                "usize" => Type::Unsigned(UnsignedNumType::Usize),
                "u8" => Type::Unsigned(UnsignedNumType::U8),
                "u16" => Type::Unsigned(UnsignedNumType::U16),
                "u32" => Type::Unsigned(UnsignedNumType::U32),
                "u64" => Type::Unsigned(UnsignedNumType::U64),
                "u128" => Type::Unsigned(UnsignedNumType::U128),
                "i8" => Type::Signed(SignedNumType::I8),
                "i16" => Type::Signed(SignedNumType::I16),
                "i32" => Type::Signed(SignedNumType::I32),
                "i64" => Type::Signed(SignedNumType::I64),
                "i128" => Type::Signed(SignedNumType::I128),
                identifier => Type::Enum(identifier.to_string()),
            };
            Ok((ty, meta))
        }
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
        self.push_error_for_next(ParseErrorEnum::Expected(t.clone()));
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
