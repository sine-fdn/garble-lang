//! Parses a stream of [`crate::scan::Tokens`] into an untyped [`crate::ast::Program`].

use std::{collections::HashMap, iter::Peekable, vec::IntoIter};

use crate::{
    ast::{
        EnumDef, Expr, ExprEnum, FnDef, Op, ParamDef, Pattern, PatternEnum, PreliminaryType,
        Program, Stmt, StmtEnum, StructDef, UnaryOp, Variant, VariantExpr, VariantExprEnum,
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
    /// The top level definition is not a valid enum or function declaration.
    InvalidTopLevelDef,
    /// Arrays of the specified size are not supported.
    InvalidArraySize,
    /// The min or max value of the range expression is invalid.
    InvalidRangeExpr,
    /// The pattern is not valid.
    InvalidPattern,
    /// The literal is not valid.
    InvalidLiteral,
    /// Expected a type, but found a non-type token.
    ExpectedType,
    /// Expected a statement, but found a non-statement token.
    ExpectedStmt,
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
            ParseErrorEnum::InvalidTopLevelDef => {
                f.write_str("Not a valid function or enum definition")
            }
            ParseErrorEnum::InvalidArraySize => {
                let max = usize::MAX;
                f.write_fmt(format_args!(
                    "Invalid array size (must be a constant number <= {max})"
                ))
            }
            ParseErrorEnum::InvalidRangeExpr => f.write_str("Invalid range expression"),
            ParseErrorEnum::InvalidPattern => f.write_str("Invalid pattern"),
            ParseErrorEnum::InvalidLiteral => f.write_str("Invalid literal"),
            ParseErrorEnum::ExpectedType => f.write_str("Expected a type"),
            ParseErrorEnum::ExpectedStmt => f.write_str("Expected a statement"),
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
    struct_literals_allowed: bool,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: vec![],
            struct_literals_allowed: true,
        }
    }

    fn parse(mut self) -> Result<Program, Vec<ParseError>> {
        let top_level_keywords = [TokenEnum::KeywordFn];
        let mut struct_defs = HashMap::new();
        let mut enum_defs = HashMap::new();
        let mut fn_defs = HashMap::new();
        let mut is_pub = None;
        while let Some(Token(token_enum, meta)) = self.tokens.next() {
            match token_enum {
                TokenEnum::KeywordPub if is_pub == None => {
                    is_pub = Some(meta);
                }
                TokenEnum::KeywordStruct => {
                    if let Ok((struct_name, struct_def)) = self.parse_struct_def(meta) {
                        struct_defs.insert(struct_name, struct_def);
                    } else {
                        self.consume_until_one_of(&top_level_keywords);
                    }
                    is_pub = None;
                }
                TokenEnum::KeywordEnum => {
                    if let Ok((enum_name, enum_def)) = self.parse_enum_def(meta) {
                        enum_defs.insert(enum_name, enum_def);
                    } else {
                        self.consume_until_one_of(&top_level_keywords);
                    }
                    is_pub = None;
                }
                TokenEnum::KeywordFn => {
                    if let Ok(fn_def) = self.parse_fn_def(is_pub.is_some(), is_pub.unwrap_or(meta))
                    {
                        fn_defs.insert(fn_def.identifier.clone(), fn_def);
                    } else {
                        self.consume_until_one_of(&top_level_keywords);
                    }
                    is_pub = None;
                }
                _ => {
                    self.push_error(ParseErrorEnum::InvalidTopLevelDef, meta);
                    self.consume_until_one_of(&top_level_keywords);
                }
            }
        }
        if self.errors.is_empty() {
            return Ok(Program {
                struct_defs,
                enum_defs,
                fn_defs,
            });
        }
        Err(self.errors)
    }

    fn parse_struct_def(&mut self, start: MetaInfo) -> Result<(String, StructDef), ()> {
        // struct keyword was already consumed by the top-level parser
        let (identifier, _) = self.expect_identifier()?;

        self.expect(&TokenEnum::LeftBrace)?;

        let mut fields = vec![];
        if !self.peek(&TokenEnum::RightBrace) {
            let (name, _) = self.expect_identifier()?;
            self.expect(&TokenEnum::Colon)?;
            let (ty, _) = self.parse_type()?;
            fields.push((name, ty));
            while self.next_matches(&TokenEnum::Comma).is_some() {
                if self.peek(&TokenEnum::RightBrace) {
                    break;
                }
                let (name, _) = self.expect_identifier()?;
                self.expect(&TokenEnum::Colon)?;
                let (ty, _) = self.parse_type()?;
                fields.push((name, ty));
            }
        }
        let end = self.expect(&TokenEnum::RightBrace)?;
        let meta = join_meta(start, end);
        fields.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
        Ok((identifier, StructDef { fields, meta }))
    }

    fn parse_enum_def(&mut self, start: MetaInfo) -> Result<(String, EnumDef), ()> {
        // enum keyword was already consumed by the top-level parser

        let (identifier, _) = self.expect_identifier()?;

        self.expect(&TokenEnum::LeftBrace)?;

        let mut variants = vec![self.parse_variant()?];

        while self.next_matches(&TokenEnum::Comma).is_some() {
            if self.peek(&TokenEnum::RightBrace) {
                break;
            }
            variants.push(self.parse_variant()?);
        }

        let end = self.expect(&TokenEnum::RightBrace)?;
        let meta = join_meta(start, end);
        Ok((identifier, EnumDef { variants, meta }))
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
                if self.peek(&TokenEnum::RightParen) {
                    break;
                }
                let (ty, _) = self.parse_type()?;
                fields.push(ty);
            }
            self.expect(&TokenEnum::RightParen)?;
            Ok(Variant::Tuple(variant_name, fields))
        } else {
            Ok(Variant::Unit(variant_name))
        }
    }

    fn parse_fn_def(&mut self, is_pub: bool, start: MetaInfo) -> Result<FnDef, ()> {
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
        let body = self.parse_stmts()?;
        let end = self.expect(&TokenEnum::RightBrace)?;

        let meta = join_meta(start, end);
        Ok(FnDef {
            is_pub,
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
        // mut <param>: <type>
        let is_mutable = self.next_matches(&TokenEnum::KeywordMut).is_some();
        let (param_name, _) = self.expect_identifier()?;
        self.expect(&TokenEnum::Colon)?;
        let (ty, _) = self.parse_type()?;
        Ok(ParamDef(is_mutable, param_name, ty))
    }

    fn parse_stmt(&mut self) -> Result<Stmt, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::KeywordLet) {
            if self.next_matches(&TokenEnum::KeywordMut).is_some() {
                // let mut <identifier> = <binding>;
                let (identifier, _) = self.expect_identifier()?;
                self.expect(&TokenEnum::Eq)?;
                if let Ok(binding) = self.parse_expr() {
                    let meta = join_meta(meta, binding.1);
                    self.expect(&TokenEnum::Semicolon)?;
                    return Ok(Stmt(StmtEnum::LetMut(identifier, binding), meta));
                } else {
                    self.push_error_for_next(ParseErrorEnum::ExpectedStmt);
                    self.consume_until_one_of(&[TokenEnum::Semicolon]);
                    self.tokens.next();
                    self.parse_expr()?;
                    self.expect(&TokenEnum::Semicolon)?;
                }
            } else {
                // let <pattern> = <binding>;
                let pattern = self.parse_pattern()?;
                self.expect(&TokenEnum::Eq)?;
                if let Ok(binding) = self.parse_expr() {
                    let meta = join_meta(meta, binding.1);
                    self.expect(&TokenEnum::Semicolon)?;
                    return Ok(Stmt(StmtEnum::Let(pattern, binding), meta));
                } else {
                    self.push_error_for_next(ParseErrorEnum::ExpectedStmt);
                    self.consume_until_one_of(&[TokenEnum::Semicolon]);
                    self.tokens.next();
                    self.parse_expr()?;
                    self.expect(&TokenEnum::Semicolon)?;
                }
            }
        } else if let Some(meta) = self.next_matches(&TokenEnum::KeywordFor) {
            // for <var> in <binding> { <body> }
            let (var, _) = self.expect_identifier()?;
            self.expect(&TokenEnum::KeywordIn)?;
            self.struct_literals_allowed = false;
            let binding = self.parse_expr()?;
            self.struct_literals_allowed = true;
            self.expect(&TokenEnum::LeftBrace)?;
            let loop_body = self.parse_stmts()?;
            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            return Ok(Stmt(StmtEnum::ForEachLoop(var, binding, loop_body), meta));
        } else {
            let is_conditional_or_block = self.peek(&TokenEnum::KeywordIf)
                || self.peek(&TokenEnum::KeywordMatch)
                || self.peek(&TokenEnum::LeftBrace);
            let expr = self.parse_expr()?;
            let meta = expr.1;
            let stmt = if let Expr(ExprEnum::Identifier(identifier), identifier_meta) = expr {
                if self.next_matches(&TokenEnum::Eq).is_some() {
                    let value = self.parse_expr()?;
                    let meta = join_meta(identifier_meta, value.1);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt(StmtEnum::VarAssign(identifier, value), meta)
                } else {
                    let expr = Expr(ExprEnum::Identifier(identifier), identifier_meta);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt(StmtEnum::Expr(expr), meta)
                }
            } else if let Expr(ExprEnum::ArrayAccess(array, index), array_meta) = expr {
                if let (Expr(ExprEnum::Identifier(identifier), _), Some(_)) =
                    (array.as_ref(), self.next_matches(&TokenEnum::Eq))
                {
                    let value = self.parse_expr()?;
                    let meta = join_meta(array_meta, value.1);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt(
                        StmtEnum::ArrayAssign(identifier.clone(), *index, value),
                        meta,
                    )
                } else {
                    let expr = Expr(ExprEnum::ArrayAccess(array, index), array_meta);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt(StmtEnum::Expr(expr), meta)
                }
            } else {
                if !is_conditional_or_block
                    && !self.peek(&TokenEnum::RightBrace)
                    && !self.peek(&TokenEnum::Comma)
                {
                    self.expect(&TokenEnum::Semicolon)?;
                }
                Stmt(StmtEnum::Expr(expr), meta)
            };
            return Ok(stmt);
        }
        Err(())
    }

    fn parse_stmts(&mut self) -> Result<Vec<Stmt>, ()> {
        let mut stmts = vec![];
        while !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
            if let Ok(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            }
        }
        if self.errors.is_empty() {
            Ok(stmts)
        } else {
            Err(())
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::LeftBrace) {
            // { ... }
            let stmts = self.parse_stmts()?;
            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            Ok(Expr(ExprEnum::Block(stmts), meta))
        } else {
            self.parse_short_circuiting_or()
        }
    }

    fn parse_block_as_expr(&mut self) -> Result<Expr, ()> {
        let stmts = self.parse_stmts()?;
        match stmts.last() {
            Some(Stmt(StmtEnum::Expr(expr), _)) if stmts.len() == 1 => Ok(expr.clone()),
            Some(Stmt(_, last)) => {
                let Stmt(_, first) = stmts.first().unwrap();
                let meta = join_meta(*first, *last);
                Ok(Expr(ExprEnum::Block(stmts), meta))
            }
            None => {
                let meta = self.tokens.peek().unwrap().1;
                Ok(Expr(ExprEnum::TupleLiteral(vec![]), meta))
            }
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
            self.struct_literals_allowed = false;
            let cond_expr = self.parse_expr()?;
            self.struct_literals_allowed = true;
            self.expect(&TokenEnum::LeftBrace)?;

            if let Ok(then_expr) = self.parse_block_as_expr() {
                let meta_right_brace = self.expect(&TokenEnum::RightBrace)?;
                if self.next_matches(&TokenEnum::KeywordElse).is_some() {
                    if self.peek(&TokenEnum::KeywordIf) {
                        let elseif_expr = self.parse_block_as_expr()?;
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

                        let else_expr = self.parse_block_as_expr()?;
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
                    let meta = join_meta(meta, meta_right_brace);
                    let else_expr = Expr(ExprEnum::TupleLiteral(vec![]), meta);
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

                let _else_expr = self.parse_block_as_expr()?;
                self.expect(&TokenEnum::RightBrace)?;

                Err(())
            }
        } else if let Some(meta) = self.next_matches(&TokenEnum::KeywordMatch) {
            // match <match_expr> { <clause> * }
            self.struct_literals_allowed = false;
            let match_expr = self.parse_expr()?;
            self.struct_literals_allowed = true;
            self.expect(&TokenEnum::LeftBrace)?;

            let mut has_failed = false;
            let mut clauses = vec![];
            let mut clause_ended_with_brace = false;
            if let Ok((clause, ends_with_brace)) = self.parse_match_clause() {
                clause_ended_with_brace = ends_with_brace;
                clauses.push(clause);
            } else {
                has_failed = true;
                self.consume_until_one_of(&[TokenEnum::Comma, TokenEnum::RightBrace]);
            }
            while self.next_matches(&TokenEnum::Comma).is_some() || clause_ended_with_brace {
                if self.peek(&TokenEnum::RightBrace) {
                    break;
                }
                if let Ok((clause, ends_with_brace)) = self.parse_match_clause() {
                    clause_ended_with_brace = ends_with_brace;
                    clauses.push(clause);
                } else {
                    has_failed = true;
                    self.consume_until_one_of(&[TokenEnum::Comma, TokenEnum::RightBrace]);
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

    fn parse_match_clause(&mut self) -> Result<((Pattern, Expr), bool), ()> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenEnum::FatArrow)?;
        let stmt = self.parse_stmt()?;
        let ends_with_brace = matches!(
            stmt.0,
            StmtEnum::Expr(Expr(ExprEnum::Match(_, _), _))
                | StmtEnum::Expr(Expr(ExprEnum::Block(_), _))
                | StmtEnum::Expr(Expr(ExprEnum::If(_, _, _), _))
        );
        let meta = stmt.1;
        let expr = Expr(ExprEnum::Block(vec![stmt]), meta);
        Ok(((pattern, expr), ends_with_brace))
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
                                    if self.peek(&TokenEnum::RightParen) {
                                        break;
                                    }
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
                    } else if self.next_matches(&TokenEnum::LeftBrace).is_some() {
                        let mut fields = vec![];
                        let mut ignore_remaining_fields = false;
                        if !self.peek(&TokenEnum::RightBrace) {
                            let (field_name, field_name_meta) = self.expect_identifier()?;
                            let field_pattern = if self.peek(&TokenEnum::Comma)
                                || self.peek(&TokenEnum::RightBrace)
                            {
                                Pattern(
                                    PatternEnum::Identifier(field_name.clone()),
                                    field_name_meta,
                                )
                            } else {
                                self.expect(&TokenEnum::Colon)?;
                                self.parse_pattern()?
                            };
                            fields.push((field_name, field_pattern));
                            while self.next_matches(&TokenEnum::Comma).is_some() {
                                if self.peek(&TokenEnum::RightBrace) {
                                    break;
                                }
                                if self.next_matches(&TokenEnum::DoubleDot).is_some() {
                                    ignore_remaining_fields = true;
                                    break;
                                }
                                let (field_name, field_name_meta) = self.expect_identifier()?;
                                let field_pattern = if self.peek(&TokenEnum::Comma)
                                    || self.peek(&TokenEnum::RightBrace)
                                {
                                    Pattern(
                                        PatternEnum::Identifier(field_name.clone()),
                                        field_name_meta,
                                    )
                                } else {
                                    self.expect(&TokenEnum::Colon)?;
                                    self.parse_pattern()?
                                };
                                fields.push((field_name, field_pattern));
                            }
                        }
                        self.expect(&TokenEnum::RightBrace)?;
                        fields.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                        if ignore_remaining_fields {
                            Ok(Pattern(
                                PatternEnum::StructIgnoreRemaining(identifier, fields),
                                meta,
                            ))
                        } else {
                            Ok(Pattern(PatternEnum::Struct(identifier, fields), meta))
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
                    if self.peek(&TokenEnum::DoubleDot) || self.peek(&TokenEnum::DoubleDotEquals) {
                        let is_inclusive = self.peek(&TokenEnum::DoubleDotEquals);
                        self.tokens.next();
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
                                        if is_inclusive {
                                            range_end
                                        } else {
                                            range_end - 1
                                        },
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
                    if self.peek(&TokenEnum::DoubleDot) || self.peek(&TokenEnum::DoubleDotEquals) {
                        let is_inclusive = self.peek(&TokenEnum::DoubleDotEquals);
                        self.tokens.next();
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
                                        if is_inclusive {
                                            range_end
                                        } else {
                                            range_end - 1
                                        },
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
                            if self.peek(&TokenEnum::RightParen) {
                                break;
                            }
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
                                    if self.peek(&TokenEnum::RightParen) {
                                        break;
                                    }
                                    args.push(self.parse_expr()?);
                                }
                            }
                            let end = self.expect(&TokenEnum::RightParen)?;
                            let meta = join_meta(meta, end);
                            Expr(ExprEnum::FnCall(identifier.to_string(), args), meta)
                        } else if self.peek(&TokenEnum::LeftBrace) && self.struct_literals_allowed {
                            // Struct literal:
                            self.parse_literal(Token(token_enum, meta), false)?
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
        while self.peek(&TokenEnum::LeftBracket) || self.peek(&TokenEnum::Dot) {
            if self.next_matches(&TokenEnum::LeftBracket).is_some() {
                if let Some(Token(TokenEnum::ConstantIndexOrSize(i), meta)) = self.tokens.peek() {
                    let i = *i;
                    let meta = *meta;
                    self.tokens.next();
                    let index = Expr(
                        ExprEnum::NumUnsigned(i as u128, UnsignedNumType::Usize),
                        meta,
                    );
                    let end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(expr.1, end);
                    expr = Expr(ExprEnum::ArrayAccess(Box::new(expr), Box::new(index)), meta);
                } else {
                    let index = self.parse_expr()?;
                    let end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(expr.1, end);
                    expr = Expr(ExprEnum::ArrayAccess(Box::new(expr), Box::new(index)), meta);
                }
            } else if self.next_matches(&TokenEnum::Dot).is_some() {
                let peeked = self.tokens.peek();
                if let Some(Token(TokenEnum::Identifier(_), _)) = peeked {
                    expr = self.parse_method_call_or_struct_access(expr)?;
                } else if let Some(Token(TokenEnum::ConstantIndexOrSize(i), meta_index)) = peeked {
                    let i = *i;
                    let meta_index = *meta_index;
                    self.tokens.next();
                    let meta = join_meta(expr.1, meta_index);
                    expr = Expr(ExprEnum::TupleAccess(Box::new(expr), i as usize), meta)
                } else {
                    self.push_error_for_next(ParseErrorEnum::ExpectedMethodCallOrFieldAccess);
                    return Err(());
                }
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
                            }
                            let end = self.expect(&TokenEnum::RightParen)?;
                            let variant_meta = join_meta(variant_meta, end);
                            VariantExpr(variant_name, VariantExprEnum::Tuple(fields), variant_meta)
                        } else {
                            VariantExpr(variant_name, VariantExprEnum::Unit, variant_meta)
                        };
                        Expr(ExprEnum::EnumLiteral(identifier, Box::new(variant)), meta)
                    } else if self.next_matches(&TokenEnum::LeftBrace).is_some()
                        && self.struct_literals_allowed
                    {
                        let mut fields = vec![];
                        if !self.peek(&TokenEnum::RightBrace) {
                            let (name, name_meta) = self.expect_identifier()?;
                            let value = if self.peek(&TokenEnum::Comma)
                                || self.peek(&TokenEnum::RightBrace)
                            {
                                Expr(ExprEnum::Identifier(name.clone()), name_meta)
                            } else {
                                self.expect(&TokenEnum::Colon)?;
                                self.parse_expr()?
                            };
                            fields.push((name, value));
                            while self.next_matches(&TokenEnum::Comma).is_some() {
                                if self.peek(&TokenEnum::RightBrace) {
                                    break;
                                }
                                let (name, name_meta) = self.expect_identifier()?;
                                let value = if self.peek(&TokenEnum::Comma)
                                    || self.peek(&TokenEnum::RightBrace)
                                {
                                    Expr(ExprEnum::Identifier(name.clone()), name_meta)
                                } else {
                                    self.expect(&TokenEnum::Colon)?;
                                    self.parse_expr()?
                                };
                                fields.push((name, value));
                            }
                        }
                        self.expect(&TokenEnum::RightBrace)?;
                        fields.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                        Expr(ExprEnum::StructLiteral(identifier, fields), meta)
                    } else {
                        self.push_error(ParseErrorEnum::InvalidLiteral, meta);
                        return Err(());
                    }
                }
            },
            TokenEnum::UnsignedNum(n, n_suffix) => {
                if self.next_matches(&TokenEnum::DoubleDot).is_some() {
                    if let Some(Token(
                        TokenEnum::UnsignedNum(range_end, range_end_suffix),
                        meta_end,
                    )) = self.tokens.peek()
                    {
                        let range_end = *range_end;
                        let range_end_suffix = *range_end_suffix;
                        let meta_end = *meta_end;
                        self.tokens.next();
                        let meta = join_meta(meta, meta_end);
                        Expr(
                            ExprEnum::Range((n, n_suffix), (range_end, range_end_suffix)),
                            meta,
                        )
                    } else {
                        self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                        return Err(());
                    }
                } else {
                    Expr(ExprEnum::NumUnsigned(n, n_suffix), meta)
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
                    let size = if let Some(Token(TokenEnum::ConstantIndexOrSize(n), _)) =
                        self.tokens.peek()
                    {
                        let n = *n;
                        self.tokens.next();
                        n as usize
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
                        if self.peek(&TokenEnum::RightBracket) {
                            break;
                        }
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

    fn parse_method_call_or_struct_access(&mut self, recv: Expr) -> Result<Expr, ()> {
        let (field, call_start) = self.expect_identifier()?;
        Ok(Expr(
            ExprEnum::StructAccess(Box::new(recv), field),
            call_start,
        ))
    }

    fn parse_type(&mut self) -> Result<(PreliminaryType, MetaInfo), ()> {
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
            Ok((PreliminaryType::Tuple(fields), meta))
        } else if let Some(meta) = self.next_matches(&TokenEnum::LeftBracket) {
            let (ty, _) = self.parse_type()?;
            self.expect(&TokenEnum::Semicolon)?;
            let size = if let Some(Token(TokenEnum::ConstantIndexOrSize(n), _)) = self.tokens.peek()
            {
                let n = *n;
                self.tokens.next();
                n as usize
            } else {
                self.push_error_for_next(ParseErrorEnum::InvalidArraySize);
                return Err(());
            };
            let meta_end = self.expect(&TokenEnum::RightBracket)?;
            let meta = join_meta(meta, meta_end);
            Ok((PreliminaryType::Array(Box::new(ty), size), meta))
        } else {
            let (ty, meta) = self.expect_identifier()?;
            let ty = match ty.as_str() {
                "bool" => PreliminaryType::Bool,
                "usize" => PreliminaryType::Unsigned(UnsignedNumType::Usize),
                "u8" => PreliminaryType::Unsigned(UnsignedNumType::U8),
                "u16" => PreliminaryType::Unsigned(UnsignedNumType::U16),
                "u32" => PreliminaryType::Unsigned(UnsignedNumType::U32),
                "u64" => PreliminaryType::Unsigned(UnsignedNumType::U64),
                "u128" => PreliminaryType::Unsigned(UnsignedNumType::U128),
                "i8" => PreliminaryType::Signed(SignedNumType::I8),
                "i16" => PreliminaryType::Signed(SignedNumType::I16),
                "i32" => PreliminaryType::Signed(SignedNumType::I32),
                "i64" => PreliminaryType::Signed(SignedNumType::I64),
                "i128" => PreliminaryType::Signed(SignedNumType::I128),
                identifier => PreliminaryType::StructOrEnum(identifier.to_string(), meta),
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
