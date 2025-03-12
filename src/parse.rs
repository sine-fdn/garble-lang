//! Parses a stream of [`crate::scan::Tokens`] into an untyped [`crate::ast::Program`].

use std::{collections::HashMap, iter::Peekable, vec::IntoIter};

use crate::{
    ast::{
        Accessor, ConstDef, ConstExpr, ConstExprEnum, EnumDef, Expr, ExprEnum, FnDef, Op, ParamDef,
        Pattern, PatternEnum, Program, Stmt, StmtEnum, StructDef, Type, UnaryOp, Variant,
        VariantExprEnum,
    },
    scan::Tokens,
    token::{MetaInfo, SignedNumType, Token, TokenEnum, UnsignedNumType},
    UntypedExpr, UntypedFnDef, UntypedPattern, UntypedProgram, UntypedStmt,
};

/// An error found during parsing, with its location in the source code.
#[derive(Debug, Clone)]
pub struct ParseError(pub ParseErrorEnum, pub MetaInfo);

#[derive(Debug, Clone)]

/// The different kinds of errors found during parsing.
pub enum ParseErrorEnum {
    /// The top level definition is not a valid enum/struct/const/fn declaration.
    InvalidTopLevelDef,
    /// Arrays of the specified size are not supported.
    InvalidArraySize,
    /// The min or max value of the range expression is invalid.
    InvalidRangeExpr,
    /// The pattern is not valid.
    InvalidPattern,
    /// The literal is not valid.
    InvalidLiteral,
    /// Expected a const expr, but found a non-const or invalid expr.
    InvalidConstExpr,
    /// The specified range has different min and max types.
    InvalidRangeTypes(UnsignedNumType, UnsignedNumType),
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
                f.write_str("Not a valid top level declaration (struct/enum/const/fn)")
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
            ParseErrorEnum::InvalidConstExpr => f.write_str("Invalid const expr"),
            ParseErrorEnum::InvalidRangeTypes(from, to) => f.write_fmt(format_args!(
                "Start and end of range do not have the same type; {from} vs {to}"
            )),
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
    pub fn parse(self) -> Result<UntypedProgram, Vec<ParseError>> {
        Parser::new(self.0).parse()
    }

    pub(crate) fn parse_literal(self) -> Result<UntypedExpr, Vec<ParseError>> {
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
    open_parens_or_brackets: Vec<TokenEnum>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            errors: vec![],
            struct_literals_allowed: true,
            open_parens_or_brackets: vec![],
        }
    }

    fn parse(mut self) -> Result<UntypedProgram, Vec<ParseError>> {
        let top_level_keywords = [
            TokenEnum::KeywordPub,
            TokenEnum::KeywordFn,
            TokenEnum::KeywordStruct,
            TokenEnum::KeywordEnum,
            TokenEnum::KeywordConst,
        ];
        let mut const_defs = HashMap::new();
        let mut struct_defs = HashMap::new();
        let mut enum_defs = HashMap::new();
        let mut fn_defs = HashMap::new();
        let mut is_pub = None;
        while let Some(Token(token_enum, meta)) = self.advance() {
            match token_enum {
                TokenEnum::KeywordPub if is_pub.is_none() => {
                    is_pub = Some(meta);
                }
                TokenEnum::KeywordConst => {
                    if let Ok((const_name, const_def)) = self.parse_const_def(meta) {
                        const_defs.insert(const_name, const_def);
                    } else {
                        self.consume_until_one_of(&top_level_keywords);
                    }
                    is_pub = None;
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
                const_deps: HashMap::new(),
                const_defs,
                struct_defs,
                enum_defs,
                fn_defs,
            });
        }
        Err(self.errors)
    }

    fn parse_const_def(&mut self, start: MetaInfo) -> Result<(String, ConstDef), ()> {
        // const keyword was already consumed by the top-level parser
        let (identifier, _) = self.expect_identifier()?;

        self.expect(&TokenEnum::Colon)?;

        let (ty, _) = self.parse_type()?;

        self.expect(&TokenEnum::Eq)?;

        let Ok(expr) = self.parse_primary() else {
            self.push_error(ParseErrorEnum::InvalidTopLevelDef, start);
            return Err(());
        };
        fn parse_const_expr(
            expr: UntypedExpr,
        ) -> Result<ConstExpr, Vec<(ParseErrorEnum, MetaInfo)>> {
            match expr.inner {
                ExprEnum::True => Ok(ConstExpr(ConstExprEnum::True, expr.meta)),
                ExprEnum::False => Ok(ConstExpr(ConstExprEnum::False, expr.meta)),
                ExprEnum::NumUnsigned(n, ty) => {
                    Ok(ConstExpr(ConstExprEnum::NumUnsigned(n, ty), expr.meta))
                }
                ExprEnum::NumSigned(n, ty) => {
                    Ok(ConstExpr(ConstExprEnum::NumSigned(n, ty), expr.meta))
                }
                ExprEnum::EnumLiteral(party, identifier, VariantExprEnum::Unit) => Ok(ConstExpr(
                    ConstExprEnum::ExternalValue { party, identifier },
                    expr.meta,
                )),
                ExprEnum::FnCall(f, args) if f == "max" || f == "min" => {
                    let mut const_exprs = vec![];
                    let mut arg_errs = vec![];
                    for arg in args {
                        match parse_const_expr(arg) {
                            Ok(value) => {
                                const_exprs.push(value);
                            }
                            Err(errs) => {
                                arg_errs.extend(errs);
                            }
                        }
                    }
                    if !arg_errs.is_empty() {
                        return Err(arg_errs);
                    }
                    if f == "max" {
                        Ok(ConstExpr(ConstExprEnum::Max(const_exprs), expr.meta))
                    } else {
                        Ok(ConstExpr(ConstExprEnum::Min(const_exprs), expr.meta))
                    }
                }
                _ => Err(vec![(ParseErrorEnum::InvalidConstExpr, expr.meta)]),
            }
        }
        match parse_const_expr(expr) {
            Ok(value) => {
                let end = self.expect(&TokenEnum::Semicolon)?;
                let meta = join_meta(start, end);
                Ok((identifier, ConstDef { ty, value, meta }))
            }
            Err(errs) => {
                for (e, meta) in errs {
                    self.push_error(e, meta);
                }
                Err(())
            }
        }
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

    fn parse_fn_def(&mut self, is_pub: bool, start: MetaInfo) -> Result<UntypedFnDef, ()> {
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
        let (name, _) = self.expect_identifier()?;
        self.expect(&TokenEnum::Colon)?;
        let (ty, _) = self.parse_type()?;
        Ok(ParamDef {
            mutability: is_mutable.into(),
            name,
            ty,
        })
    }

    fn parse_stmt(&mut self) -> Result<UntypedStmt, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::KeywordLet) {
            if self.next_matches(&TokenEnum::KeywordMut).is_some() {
                // let mut <identifier> = <binding>;
                let (identifier, _) = self.expect_identifier()?;
                let ty = if self.next_matches(&TokenEnum::Colon).is_some() {
                    let (ty, _) = self.parse_type()?;
                    Some(ty)
                } else {
                    None
                };
                self.expect(&TokenEnum::Eq)?;
                if let Ok(binding) = self.parse_expr() {
                    let meta = join_meta(meta, binding.meta);
                    self.expect(&TokenEnum::Semicolon)?;
                    return Ok(Stmt::new(StmtEnum::LetMut(identifier, ty, binding), meta));
                } else {
                    self.push_error_for_next(ParseErrorEnum::ExpectedStmt);
                    self.consume_until_one_of(&[TokenEnum::Semicolon]);
                    self.advance();
                    self.parse_expr()?;
                    self.expect(&TokenEnum::Semicolon)?;
                }
            } else {
                // let <pattern> = <binding>;
                let pattern = self.parse_pattern()?;
                let ty = if self.next_matches(&TokenEnum::Colon).is_some() {
                    let (ty, _) = self.parse_type()?;
                    Some(ty)
                } else {
                    None
                };
                self.expect(&TokenEnum::Eq)?;
                if let Ok(binding) = self.parse_expr() {
                    let meta = join_meta(meta, binding.meta);
                    self.expect(&TokenEnum::Semicolon)?;
                    return Ok(Stmt::new(StmtEnum::Let(pattern, ty, binding), meta));
                } else {
                    self.consume_until_one_of(&[TokenEnum::Semicolon]);
                    self.expect(&TokenEnum::Semicolon)?;
                }
            }
        } else if let Some(meta) = self.next_matches(&TokenEnum::KeywordFor) {
            // for <pattern> in <binding> { <body> }
            let pattern = self.parse_pattern()?;
            self.expect(&TokenEnum::KeywordIn)?;
            self.struct_literals_allowed = false;
            let binding = self.parse_expr()?;
            self.struct_literals_allowed = true;
            self.expect(&TokenEnum::LeftBrace)?;
            let loop_body = self.parse_stmts()?;
            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            return Ok(Stmt::new(
                StmtEnum::ForEachLoop(pattern, binding, loop_body),
                meta,
            ));
        } else {
            let is_conditional_or_block = self.peek(&TokenEnum::KeywordIf)
                || self.peek(&TokenEnum::KeywordMatch)
                || self.peek(&TokenEnum::LeftBrace);
            let expr = self.parse_expr()?;
            let meta = expr.meta;
            let stmt = if let ExprEnum::Identifier(identifier) = expr.inner {
                if self.next_matches(&TokenEnum::Eq).is_some() {
                    let value = self.parse_expr()?;
                    let meta = join_meta(meta, value.meta);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt::new(StmtEnum::VarAssign(identifier, vec![], value), meta)
                } else if let Some(Token(next, _)) = self.tokens.peek() {
                    let op = match next {
                        TokenEnum::AddAssign => Some(Op::Add),
                        TokenEnum::SubAssign => Some(Op::Sub),
                        TokenEnum::MulAssign => Some(Op::Mul),
                        TokenEnum::DivAssign => Some(Op::Div),
                        TokenEnum::RemAssign => Some(Op::Mod),
                        TokenEnum::BitXorAssign => Some(Op::BitXor),
                        TokenEnum::BitAndAssign => Some(Op::BitAnd),
                        TokenEnum::BitOrAssign => Some(Op::BitOr),
                        TokenEnum::ShrAssign => Some(Op::ShiftRight),
                        TokenEnum::ShlAssign => Some(Op::ShiftLeft),
                        _ => None,
                    };
                    if let Some(op) = op {
                        self.advance();
                        let value = self.parse_expr()?;
                        let identifier_meta = meta;
                        let meta = join_meta(meta, value.meta);
                        if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                            self.expect(&TokenEnum::Semicolon)?;
                        }
                        let binary_op = Expr::untyped(
                            ExprEnum::Op(
                                op,
                                Box::new(Expr::untyped(
                                    ExprEnum::Identifier(identifier.clone()),
                                    identifier_meta,
                                )),
                                Box::new(value),
                            ),
                            meta,
                        );
                        Stmt::new(StmtEnum::VarAssign(identifier, vec![], binary_op), meta)
                    } else {
                        let expr = Expr::untyped(ExprEnum::Identifier(identifier), meta);
                        if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                            self.expect(&TokenEnum::Semicolon)?;
                        }
                        Stmt::new(StmtEnum::Expr(expr), meta)
                    }
                } else {
                    let expr = Expr::untyped(ExprEnum::Identifier(identifier), meta);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt::new(StmtEnum::Expr(expr), meta)
                }
            } else if let ExprEnum::ArrayAccess(array, index) = expr.inner {
                if let (ExprEnum::Identifier(identifier), Some(_)) =
                    (&array.as_ref().inner, self.next_matches(&TokenEnum::Eq))
                {
                    let value = self.parse_expr()?;
                    let meta = join_meta(meta, value.meta);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt::new(
                        StmtEnum::VarAssign(
                            identifier.clone(),
                            vec![Accessor::ArrayAccess {
                                array_ty: (),
                                index: *index,
                            }],
                            value,
                        ),
                        meta,
                    )
                } else {
                    let expr = Expr::untyped(ExprEnum::ArrayAccess(array, index), meta);
                    if !self.peek(&TokenEnum::RightBrace) && !self.peek(&TokenEnum::Comma) {
                        self.expect(&TokenEnum::Semicolon)?;
                    }
                    Stmt::new(StmtEnum::Expr(expr), meta)
                }
            } else {
                if !is_conditional_or_block
                    && !self.peek(&TokenEnum::RightBrace)
                    && !self.peek(&TokenEnum::Comma)
                {
                    self.expect(&TokenEnum::Semicolon)?;
                }
                Stmt::new(StmtEnum::Expr(expr), meta)
            };
            return Ok(stmt);
        }
        Err(())
    }

    fn parse_stmts(&mut self) -> Result<Vec<UntypedStmt>, ()> {
        let mut stmts = vec![];
        let mut has_error = false;
        while self.tokens.peek().is_some()
            && !self.peek(&TokenEnum::RightBrace)
            && !self.peek(&TokenEnum::Comma)
            && !self.peek(&TokenEnum::KeywordPub)
            && !self.peek(&TokenEnum::KeywordFn)
            && !self.peek(&TokenEnum::KeywordStruct)
            && !self.peek(&TokenEnum::KeywordEnum)
        {
            if let Ok(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            } else {
                has_error = true;
                let balanced =
                    self.consume_until_one_of(&[TokenEnum::Semicolon, TokenEnum::RightBrace]);
                if balanced {
                    self.advance();
                }
                if self.peek(&TokenEnum::Semicolon) {
                    self.advance();
                }
            }
        }
        if !has_error {
            Ok(stmts)
        } else {
            Err(())
        }
    }

    fn parse_expr(&mut self) -> Result<UntypedExpr, ()> {
        if let Some(meta) = self.next_matches(&TokenEnum::LeftBrace) {
            // { ... }
            let stmts = self.parse_stmts()?;
            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            Ok(Expr::untyped(ExprEnum::Block(stmts), meta))
        } else {
            self.parse_short_circuiting_or()
        }
    }

    fn parse_block_as_expr(&mut self) -> Result<UntypedExpr, ()> {
        let stmts = self.parse_stmts()?;
        match stmts.last() {
            Some(Stmt {
                inner: StmtEnum::Expr(expr),
                ..
            }) if stmts.len() == 1 => Ok(expr.clone()),
            Some(Stmt { meta: last, .. }) => {
                let first = stmts.first().unwrap().meta;
                let meta = join_meta(first, *last);
                Ok(Expr::untyped(ExprEnum::Block(stmts), meta))
            }
            None => {
                let meta = self.tokens.peek().unwrap().1;
                Ok(Expr::untyped(ExprEnum::TupleLiteral(vec![]), meta))
            }
        }
    }

    fn parse_short_circuiting_or(&mut self) -> Result<UntypedExpr, ()> {
        // ||
        let mut x = self.parse_short_circuiting_and()?;
        while self.next_matches(&TokenEnum::DoubleBar).is_some() {
            let y = self.parse_short_circuiting_and()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr::untyped(
                ExprEnum::Op(Op::ShortCircuitOr, Box::new(x), Box::new(y)),
                meta,
            );
        }
        Ok(x)
    }

    fn parse_short_circuiting_and(&mut self) -> Result<UntypedExpr, ()> {
        // &&
        let mut x = self.parse_equality()?;
        while self.next_matches(&TokenEnum::DoubleAmpersand).is_some() {
            let y = self.parse_equality()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr::untyped(
                ExprEnum::Op(Op::ShortCircuitAnd, Box::new(x), Box::new(y)),
                meta,
            );
        }
        Ok(x)
    }

    fn parse_equality(&mut self) -> Result<UntypedExpr, ()> {
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
            x = Expr::untyped(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_comparison(&mut self) -> Result<UntypedExpr, ()> {
        // >, <, <=, >=
        let ops = vec![
            TokenEnum::LessThan,
            TokenEnum::GreaterThan,
            TokenEnum::LessThanEquals,
            TokenEnum::GreaterThanEquals,
        ];
        let mut x = self.parse_or()?;
        while let Some((token, _)) = self.next_matches_one_of(&ops) {
            let y = self.parse_or()?;
            let meta = join_expr_meta(&x, &y);
            x = match token {
                TokenEnum::LessThan => {
                    Expr::untyped(ExprEnum::Op(Op::LessThan, Box::new(x), Box::new(y)), meta)
                }
                TokenEnum::GreaterThan => Expr::untyped(
                    ExprEnum::Op(Op::GreaterThan, Box::new(x), Box::new(y)),
                    meta,
                ),
                TokenEnum::LessThanEquals => {
                    let lt = Expr::untyped(
                        ExprEnum::Op(Op::LessThan, Box::new(x.clone()), Box::new(y.clone())),
                        meta,
                    );
                    let eq = Expr::untyped(ExprEnum::Op(Op::Eq, Box::new(x), Box::new(y)), meta);
                    Expr::untyped(ExprEnum::Op(Op::BitOr, Box::new(lt), Box::new(eq)), meta)
                }
                TokenEnum::GreaterThanEquals => {
                    let lt = Expr::untyped(
                        ExprEnum::Op(Op::GreaterThan, Box::new(x.clone()), Box::new(y.clone())),
                        meta,
                    );
                    let eq = Expr::untyped(ExprEnum::Op(Op::Eq, Box::new(x), Box::new(y)), meta);
                    Expr::untyped(ExprEnum::Op(Op::BitOr, Box::new(lt), Box::new(eq)), meta)
                }
                _ => unreachable!(),
            }
        }
        Ok(x)
    }

    fn parse_or(&mut self) -> Result<UntypedExpr, ()> {
        // |
        let mut x = self.parse_xor()?;
        while self.next_matches(&TokenEnum::Bar).is_some() {
            let y = self.parse_xor()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr::untyped(ExprEnum::Op(Op::BitOr, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_xor(&mut self) -> Result<UntypedExpr, ()> {
        // ^
        let mut x = self.parse_and()?;
        while self.next_matches(&TokenEnum::Caret).is_some() {
            let y = self.parse_and()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr::untyped(ExprEnum::Op(Op::BitXor, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_and(&mut self) -> Result<UntypedExpr, ()> {
        // &
        let mut x = self.parse_shift()?;
        while self.next_matches(&TokenEnum::Ampersand).is_some() {
            let y = self.parse_shift()?;
            let meta = join_expr_meta(&x, &y);
            x = Expr::untyped(ExprEnum::Op(Op::BitAnd, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_shift(&mut self) -> Result<UntypedExpr, ()> {
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
            x = Expr::untyped(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_term(&mut self) -> Result<UntypedExpr, ()> {
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
            x = Expr::untyped(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_factor(&mut self) -> Result<UntypedExpr, ()> {
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
            x = Expr::untyped(ExprEnum::Op(op, Box::new(x), Box::new(y)), meta);
        }
        Ok(x)
    }

    fn parse_cast(&mut self) -> Result<UntypedExpr, ()> {
        let mut x = self.parse_if_or_match()?;
        while self.next_matches(&TokenEnum::KeywordAs).is_some() {
            let (ty, ty_meta) = self.parse_type()?;
            let meta = join_meta(x.meta, ty_meta);
            x = Expr::untyped(ExprEnum::Cast(ty, Box::new(x)), meta)
        }
        Ok(x)
    }

    fn parse_if_or_match(&mut self) -> Result<UntypedExpr, ()> {
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
                        let elseif_expr = self.parse_expr()?;
                        let meta = join_meta(meta, elseif_expr.meta);
                        Ok(Expr::untyped(
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
                        Ok(Expr::untyped(
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
                    let else_expr = Expr::untyped(ExprEnum::TupleLiteral(vec![]), meta);
                    Ok(Expr::untyped(
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
                self.advance();
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
                    self.advance();
                }
            }
            if has_failed {
                return Err(());
            }

            let meta_end = self.expect(&TokenEnum::RightBrace)?;
            let meta = join_meta(meta, meta_end);
            Ok(Expr::untyped(
                ExprEnum::Match(Box::new(match_expr), clauses),
                meta,
            ))
        } else {
            self.parse_unary()
        }
    }

    fn parse_match_clause(&mut self) -> Result<((UntypedPattern, UntypedExpr), bool), ()> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenEnum::FatArrow)?;
        let stmt = self.parse_stmt()?;
        let ends_with_brace = matches!(
            stmt.inner,
            StmtEnum::Expr(Expr {
                inner: ExprEnum::Match(_, _,),
                ..
            }) | StmtEnum::Expr(Expr {
                inner: ExprEnum::Block(_),
                ..
            }) | StmtEnum::Expr(Expr {
                inner: ExprEnum::If(_, _, _),
                ..
            })
        );
        let meta = stmt.meta;
        let expr = Expr::untyped(ExprEnum::Block(vec![stmt]), meta);
        Ok(((pattern, expr), ends_with_brace))
    }

    fn parse_pattern(&mut self) -> Result<UntypedPattern, ()> {
        if let Some(Token(token_enum, meta)) = self.tokens.peek() {
            match token_enum {
                TokenEnum::Identifier(identifier) => {
                    let identifier = identifier.clone();
                    let meta = *meta;
                    self.advance();
                    match identifier.as_str() {
                        "true" => return Ok(Pattern::untyped(PatternEnum::True, meta)),
                        "false" => return Ok(Pattern::untyped(PatternEnum::False, meta)),
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
                            Ok(Pattern::untyped(
                                PatternEnum::EnumTuple(identifier, variant_name, fields),
                                meta,
                            ))
                        } else {
                            let meta = join_meta(meta, variant_meta);
                            Ok(Pattern::untyped(
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
                                Pattern::untyped(
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
                                    Pattern::untyped(
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
                            Ok(Pattern::untyped(
                                PatternEnum::StructIgnoreRemaining(identifier, fields),
                                meta,
                            ))
                        } else {
                            Ok(Pattern::untyped(
                                PatternEnum::Struct(identifier, fields),
                                meta,
                            ))
                        }
                    } else {
                        Ok(Pattern::untyped(PatternEnum::Identifier(identifier), meta))
                    }
                }
                TokenEnum::UnsignedNum(n, type_suffix) => {
                    let n = *n;
                    let type_suffix = *type_suffix;
                    let meta = *meta;
                    self.advance();
                    if self.peek(&TokenEnum::DoubleDot) || self.peek(&TokenEnum::DoubleDotEquals) {
                        let is_inclusive = self.peek(&TokenEnum::DoubleDotEquals);
                        self.advance();
                        if let Some(Token(
                            TokenEnum::UnsignedNum(range_end, type_suffix_end),
                            meta_end,
                        )) = self.tokens.peek()
                        {
                            if type_suffix == *type_suffix_end {
                                let range_end = *range_end;
                                let meta_end = *meta_end;
                                self.advance();

                                let meta = join_meta(meta, meta_end);
                                Ok(Pattern::untyped(
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
                        Ok(Pattern::untyped(
                            PatternEnum::NumUnsigned(n, type_suffix),
                            meta,
                        ))
                    }
                }
                TokenEnum::SignedNum(n, type_suffix) => {
                    let n = *n;
                    let meta = *meta;
                    let type_suffix = *type_suffix;
                    self.advance();
                    if self.peek(&TokenEnum::DoubleDot) || self.peek(&TokenEnum::DoubleDotEquals) {
                        let is_inclusive = self.peek(&TokenEnum::DoubleDotEquals);
                        self.advance();
                        if let Some(Token(
                            TokenEnum::SignedNum(range_end, type_suffix_end),
                            meta_end,
                        )) = self.tokens.peek()
                        {
                            if type_suffix == *type_suffix_end {
                                let range_end = *range_end;
                                let meta_end = *meta_end;
                                self.advance();

                                let meta = join_meta(meta, meta_end);
                                Ok(Pattern::untyped(
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
                        Ok(Pattern::untyped(
                            PatternEnum::NumSigned(n, type_suffix),
                            meta,
                        ))
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
                    Ok(Pattern::untyped(PatternEnum::Tuple(fields), meta))
                }
                _ => {
                    self.push_error_for_next(ParseErrorEnum::InvalidPattern);
                    self.consume_until_one_of(&[TokenEnum::FatArrow]);
                    self.advance();
                    Err(())
                }
            }
        } else {
            self.push_error_for_next(ParseErrorEnum::InvalidPattern);
            Err(())
        }
    }

    fn parse_unary(&mut self) -> Result<UntypedExpr, ()> {
        // -, !
        if let Some(meta) = self.next_matches(&TokenEnum::Bang) {
            let unary = self.parse_unary()?;
            let expr_meta = unary.meta;
            let meta = join_meta(meta, expr_meta);
            Ok(Expr::untyped(
                ExprEnum::UnaryOp(UnaryOp::Not, Box::new(unary)),
                meta,
            ))
        } else if let Some(meta) = self.next_matches(&TokenEnum::Minus) {
            let unary = self.parse_unary()?;
            let expr_meta = unary.meta;
            let meta = join_meta(meta, expr_meta);
            Ok(Expr::untyped(
                ExprEnum::UnaryOp(UnaryOp::Neg, Box::new(unary)),
                meta,
            ))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<UntypedExpr, ()> {
        let mut expr = if let Some(Token(token_enum, meta)) = self.advance() {
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
                            Expr::untyped(ExprEnum::FnCall(identifier.to_string(), args), meta)
                        } else if self.peek(&TokenEnum::LeftBrace) && self.struct_literals_allowed {
                            // Struct literal:
                            self.parse_literal(Token(token_enum, meta), false)?
                        } else {
                            Expr::untyped(ExprEnum::Identifier(identifier.to_string()), meta)
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
                if let Some(Token(TokenEnum::UnsignedNum(i, UnsignedNumType::Unspecified), meta)) =
                    self.tokens.peek()
                {
                    let i = *i;
                    let meta = *meta;
                    self.advance();
                    let index =
                        Expr::untyped(ExprEnum::NumUnsigned(i, UnsignedNumType::Usize), meta);
                    let end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(expr.meta, end);
                    expr =
                        Expr::untyped(ExprEnum::ArrayAccess(Box::new(expr), Box::new(index)), meta);
                } else {
                    let index = self.parse_expr()?;
                    let end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(expr.meta, end);
                    expr =
                        Expr::untyped(ExprEnum::ArrayAccess(Box::new(expr), Box::new(index)), meta);
                }
            } else if self.next_matches(&TokenEnum::Dot).is_some() {
                let peeked = self.tokens.peek();
                if let Some(Token(TokenEnum::Identifier(_), _)) = peeked {
                    expr = self.parse_method_call_or_struct_access(expr)?;
                } else if let Some(Token(
                    TokenEnum::UnsignedNum(i, UnsignedNumType::Unspecified),
                    meta_index,
                )) = peeked
                {
                    let i = *i;
                    let meta_index = *meta_index;
                    self.advance();
                    let meta = join_meta(expr.meta, meta_index);
                    expr = Expr::untyped(ExprEnum::TupleAccess(Box::new(expr), i as usize), meta)
                } else {
                    self.push_error_for_next(ParseErrorEnum::ExpectedMethodCallOrFieldAccess);
                    return Err(());
                }
            }
        }
        Ok(expr)
    }

    fn parse_literal_recusively(&mut self) -> Result<UntypedExpr, ()> {
        if let Some(token) = self.advance() {
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

    fn parse_literal(
        &mut self,
        token: Token,
        only_literal_children: bool,
    ) -> Result<UntypedExpr, ()> {
        let Token(token_enum, meta) = token;
        Ok(match token_enum {
            TokenEnum::Identifier(identifier) => match identifier.as_str() {
                "true" => Expr::untyped(ExprEnum::True, meta),
                "false" => Expr::untyped(ExprEnum::False, meta),
                _ => {
                    if self.next_matches(&TokenEnum::DoubleColon).is_some() {
                        let (variant_name, variant_meta) = self.expect_identifier()?;
                        let meta = join_meta(meta, variant_meta);
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
                            self.expect(&TokenEnum::RightParen)?;
                            VariantExprEnum::Tuple(fields)
                        } else {
                            VariantExprEnum::Unit
                        };
                        Expr::untyped(
                            ExprEnum::EnumLiteral(identifier, variant_name, variant),
                            meta,
                        )
                    } else if self.next_matches(&TokenEnum::LeftBrace).is_some()
                        && self.struct_literals_allowed
                    {
                        let mut fields = vec![];
                        if !self.peek(&TokenEnum::RightBrace) {
                            let (name, name_meta) = self.expect_identifier()?;
                            let value = if self.peek(&TokenEnum::Comma)
                                || self.peek(&TokenEnum::RightBrace)
                            {
                                Expr::untyped(ExprEnum::Identifier(name.clone()), name_meta)
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
                                    Expr::untyped(ExprEnum::Identifier(name.clone()), name_meta)
                                } else {
                                    self.expect(&TokenEnum::Colon)?;
                                    self.parse_expr()?
                                };
                                fields.push((name, value));
                            }
                        }
                        self.expect(&TokenEnum::RightBrace)?;
                        fields.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                        Expr::untyped(ExprEnum::StructLiteral(identifier, fields), meta)
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
                        self.advance();
                        let meta = join_meta(meta, meta_end);
                        let num_ty = match (n_suffix, range_end_suffix) {
                            (UnsignedNumType::Unspecified, ty)
                            | (ty, UnsignedNumType::Unspecified) => ty,
                            (ty1, ty2) if ty1 == ty2 => ty1,
                            (ty1, ty2) => {
                                self.push_error(ParseErrorEnum::InvalidRangeTypes(ty1, ty2), meta);
                                ty1
                            }
                        };
                        Expr::untyped(ExprEnum::Range(n, range_end, num_ty), meta)
                    } else {
                        self.push_error_for_next(ParseErrorEnum::InvalidRangeExpr);
                        return Err(());
                    }
                } else {
                    Expr::untyped(ExprEnum::NumUnsigned(n, n_suffix), meta)
                }
            }
            TokenEnum::SignedNum(n, type_suffix) => {
                Expr::untyped(ExprEnum::NumSigned(n, type_suffix), meta)
            }
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
                        Expr::untyped(ExprEnum::TupleLiteral(fields), meta)
                    } else {
                        self.expect(&TokenEnum::RightParen)?;
                        expr
                    }
                } else {
                    Expr::untyped(ExprEnum::TupleLiteral(vec![]), meta)
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
                    match self.tokens.peek().cloned() {
                        Some(Token(
                            TokenEnum::UnsignedNum(
                                n,
                                UnsignedNumType::Unspecified | UnsignedNumType::Usize,
                            ),
                            _,
                        )) => {
                            self.advance();
                            let meta_end = self.expect(&TokenEnum::RightBracket)?;
                            let meta = join_meta(meta, meta_end);
                            let size = n as usize;
                            Expr::untyped(ExprEnum::ArrayRepeatLiteral(Box::new(elem), size), meta)
                        }
                        Some(Token(TokenEnum::Identifier(n), _)) => {
                            self.advance();
                            let meta_end = self.expect(&TokenEnum::RightBracket)?;
                            let meta = join_meta(meta, meta_end);
                            Expr::untyped(
                                ExprEnum::ArrayRepeatLiteralConst(Box::new(elem), n),
                                meta,
                            )
                        }
                        _ => {
                            self.push_error_for_next(ParseErrorEnum::InvalidArraySize);
                            return Err(());
                        }
                    }
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
                    Expr::untyped(ExprEnum::ArrayLiteral(elems), meta)
                }
            }
            _ => {
                self.push_error(ParseErrorEnum::ExpectedExpr, meta);
                return Err(());
            }
        })
    }

    fn parse_method_call_or_struct_access(&mut self, recv: UntypedExpr) -> Result<UntypedExpr, ()> {
        let (field, call_start) = self.expect_identifier()?;
        Ok(Expr::untyped(
            ExprEnum::StructAccess(Box::new(recv), field),
            call_start,
        ))
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
            match self.tokens.peek().cloned() {
                Some(Token(
                    TokenEnum::UnsignedNum(
                        n,
                        UnsignedNumType::Unspecified | UnsignedNumType::Usize,
                    ),
                    _,
                )) => {
                    self.advance();
                    let size = n as usize;
                    let meta_end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(meta, meta_end);
                    Ok((Type::Array(Box::new(ty), size), meta))
                }
                Some(Token(TokenEnum::Identifier(n), _)) => {
                    self.advance();
                    let meta_end = self.expect(&TokenEnum::RightBracket)?;
                    let meta = join_meta(meta, meta_end);
                    Ok((Type::ArrayConst(Box::new(ty), n), meta))
                }
                _ => {
                    self.push_error_for_next(ParseErrorEnum::InvalidArraySize);
                    return Err(());
                }
            }
        } else {
            let (ty, meta) = self.expect_identifier()?;
            let ty = match ty.as_str() {
                "bool" => Type::Bool,
                "usize" => Type::Unsigned(UnsignedNumType::Usize),
                "u8" => Type::Unsigned(UnsignedNumType::U8),
                "u16" => Type::Unsigned(UnsignedNumType::U16),
                "u32" => Type::Unsigned(UnsignedNumType::U32),
                "u64" => Type::Unsigned(UnsignedNumType::U64),
                "i8" => Type::Signed(SignedNumType::I8),
                "i16" => Type::Signed(SignedNumType::I16),
                "i32" => Type::Signed(SignedNumType::I32),
                "i64" => Type::Signed(SignedNumType::I64),
                identifier => Type::UntypedTopLevelDefinition(identifier.to_string(), meta),
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
                let Token(token, _) = self.tokens.next().unwrap();
                match token {
                    TokenEnum::LeftParen | TokenEnum::LeftBrace | TokenEnum::LeftBracket => {
                        self.open_parens_or_brackets.push(token);
                    }
                    TokenEnum::RightParen | TokenEnum::RightBrace | TokenEnum::RightBracket => {
                        if let Some(last_open) = self.open_parens_or_brackets.last() {
                            if last_open == &token {
                                self.open_parens_or_brackets.pop();
                            }
                        }
                    }
                    _ => {}
                }
                return Ok(meta);
            }
        }
        self.push_error_for_next(ParseErrorEnum::Expected(t.clone()));
        Err(())
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
        self.advance();
    }

    fn advance(&mut self) -> Option<Token> {
        if let Some(Token(token, meta)) = self.tokens.next() {
            match token {
                TokenEnum::LeftParen | TokenEnum::LeftBrace | TokenEnum::LeftBracket => {
                    self.open_parens_or_brackets.push(token.clone());
                }
                TokenEnum::RightParen | TokenEnum::RightBrace | TokenEnum::RightBracket => {
                    if let Some(last_open) = self.open_parens_or_brackets.last() {
                        if last_open == &token {
                            self.open_parens_or_brackets.pop();
                        }
                    }
                }
                _ => {}
            }
            Some(Token(token, meta))
        } else {
            None
        }
    }

    fn consume_until_one_of(&mut self, options: &[TokenEnum]) -> bool {
        self.struct_literals_allowed = true;
        self.open_parens_or_brackets.clear();
        let mut balanced = true;
        while let Some(Token(token_enum, _)) = self.tokens.peek() {
            match token_enum {
                TokenEnum::LeftParen | TokenEnum::LeftBrace | TokenEnum::LeftBracket => {
                    self.open_parens_or_brackets.push(token_enum.clone());
                }
                TokenEnum::RightBrace | TokenEnum::RightParen | TokenEnum::RightBracket => {
                    if let Some(t) = self.open_parens_or_brackets.pop() {
                        match (&t, token_enum) {
                            (&TokenEnum::LeftParen, &TokenEnum::RightParen)
                            | (&TokenEnum::LeftBracket, &TokenEnum::RightBracket)
                            | (&TokenEnum::LeftBrace, &TokenEnum::RightBrace) => {}
                            _ => {
                                balanced = false;
                            }
                        }
                    } else {
                        balanced = false;
                    }
                }
                _ => {}
            }
            for option in options {
                if self.open_parens_or_brackets.is_empty() && option == token_enum {
                    return balanced;
                }
            }
            self.tokens.next();
        }
        balanced
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
            let Token(token, meta) = self.tokens.next().unwrap();
            match token {
                TokenEnum::LeftParen | TokenEnum::LeftBrace | TokenEnum::LeftBracket => {
                    self.open_parens_or_brackets.push(token);
                }
                TokenEnum::RightParen | TokenEnum::RightBrace | TokenEnum::RightBracket => {
                    if let Some(last_open) = self.open_parens_or_brackets.last() {
                        if last_open == &token {
                            self.open_parens_or_brackets.pop();
                        }
                    }
                }
                _ => {}
            }
            return Some(meta);
        }
        None
    }

    fn peek(&mut self, t: &TokenEnum) -> bool {
        if let Some(Token(next_token, _)) = self.tokens.peek() {
            return next_token == t;
        }
        false
    }
}

fn join_expr_meta(x: &UntypedExpr, y: &UntypedExpr) -> MetaInfo {
    join_meta(x.meta, y.meta)
}

fn join_meta(x: MetaInfo, y: MetaInfo) -> MetaInfo {
    MetaInfo {
        start: x.start,
        end: y.end,
    }
}
