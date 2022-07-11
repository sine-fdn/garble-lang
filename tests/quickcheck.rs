use garble_lang::{
    ast::Op::{self, *},
    ast::Type,
    compile,
    eval::{EvalError, Evaluator},
    literal::Literal::{self, NumSigned, NumUnsigned},
    token::{SignedNumType::*, UnsignedNumType::*},
    Error,
};
use quickcheck::Arbitrary;
use quickcheck_macros::quickcheck;

#[derive(Debug, Clone)]
struct OperatorTestCase {
    x: Literal,
    y: Literal,
    result: Option<Literal>,
    prg: String,
}

impl Arbitrary for OperatorTestCase {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let ops = [
            Add,
            Sub,
            Mul,
            Div,
            Mod,
            BitAnd,
            BitXor,
            BitOr,
            GreaterThan,
            LessThan,
            Eq,
            NotEq,
            ShiftLeft,
            ShiftRight,
        ];
        let op = g.choose(&ops).unwrap();
        let num_tys = [
            Type::Unsigned(U8),
            Type::Unsigned(U16),
            Type::Unsigned(U32),
            Type::Unsigned(U64),
            Type::Signed(I8),
            Type::Signed(I16),
            Type::Signed(I32),
            Type::Signed(I64),
        ];
        let (x, ty_x, y, ty_y, result, ty_result, op) = match op {
            Add | Sub | Mul | Div | Mod | BitAnd | BitXor | BitOr => {
                let ty = g.choose(&num_tys).unwrap();
                let x = arbitrary_literal_of_ty(g, ty);
                let y = arbitrary_literal_of_ty(g, ty);
                let result = apply_operator(op, &x, &y);
                (x, ty.clone(), y, ty.clone(), result, ty.clone(), op)
            }
            GreaterThan | LessThan | Eq | NotEq => {
                let ty = g.choose(&num_tys).unwrap();
                let x = arbitrary_literal_of_ty(g, ty);
                let y = arbitrary_literal_of_ty(g, ty);
                let result = apply_operator(op, &x, &y);
                (x, ty.clone(), y, ty.clone(), result, Type::Bool, op)
            }
            ShiftLeft => {
                let ty = g.choose(&num_tys).unwrap();
                let ty_u8 = Type::Unsigned(U8);
                let x = arbitrary_literal_of_ty(g, ty);
                let y_u8 = u8::arbitrary(g);
                let y = NumUnsigned(y_u8 as u64, U8);
                let result = match x {
                    NumUnsigned(x, unsigned_ty) => match unsigned_ty {
                        Usize => unreachable!("usize types must not be tested"),
                        U8 => (x as u8).checked_shl(y_u8 as u32).map(|z| z.into()),
                        U16 => (x as u16).checked_shl(y_u8 as u32).map(|z| z.into()),
                        U32 => (x as u32).checked_shl(y_u8 as u32).map(|z| z.into()),
                        U64 => (x as u64).checked_shl(y_u8 as u32).map(|z| z.into()),
                    },
                    NumSigned(x, signed_ty) => match signed_ty {
                        I8 => (x as i8).checked_shl(y_u8 as u32).map(|z| z.into()),
                        I16 => (x as i16).checked_shl(y_u8 as u32).map(|z| z.into()),
                        I32 => (x as i32).checked_shl(y_u8 as u32).map(|z| z.into()),
                        I64 => (x as i64).checked_shl(y_u8 as u32).map(|z| z.into()),
                    },
                    _ => unreachable!("shift expects a num type"),
                };
                (x, ty.clone(), y, ty_u8, result, ty.clone(), op)
            }
            ShiftRight => {
                let ty = g.choose(&num_tys).unwrap();
                let ty_u8 = Type::Unsigned(U8);
                let x = arbitrary_literal_of_ty(g, ty);
                let y_u8 = u8::arbitrary(g);
                let y = NumUnsigned(y_u8 as u64, U8);
                let result = match x {
                    NumUnsigned(x, unsigned_ty) => match unsigned_ty {
                        Usize => unreachable!("usize types must not be tested"),
                        U8 => (x as u8).checked_shr(y_u8 as u32).map(|z| z.into()),
                        U16 => (x as u16).checked_shr(y_u8 as u32).map(|z| z.into()),
                        U32 => (x as u32).checked_shr(y_u8 as u32).map(|z| z.into()),
                        U64 => (x as u64).checked_shr(y_u8 as u32).map(|z| z.into()),
                    },
                    NumSigned(x, signed_ty) => match signed_ty {
                        I8 => (x as i8).checked_shr(y_u8 as u32).map(|z| z.into()),
                        I16 => (x as i16).checked_shr(y_u8 as u32).map(|z| z.into()),
                        I32 => (x as i32).checked_shr(y_u8 as u32).map(|z| z.into()),
                        I64 => (x as i64).checked_shr(y_u8 as u32).map(|z| z.into()),
                    },
                    _ => unreachable!("shift expects a num type"),
                };
                (x, ty.clone(), y, ty_u8, result, ty.clone(), op)
            }
            ShortCircuitAnd | ShortCircuitOr => unreachable!("&& and || expect bool types"),
        };
        let prg = format!("pub fn main(x: {ty_x}, y: {ty_y}) -> {ty_result} {{ x {op} y }}");
        OperatorTestCase { x, y, result, prg }
    }
}

fn arbitrary_literal_of_ty(g: &mut quickcheck::Gen, ty: &Type) -> Literal {
    match ty {
        Type::Unsigned(ty) => match ty {
            Usize => unreachable!("usize is not supported"),
            U8 => NumUnsigned(u8::arbitrary(g) as u64, *ty),
            U16 => NumUnsigned(u16::arbitrary(g) as u64, *ty),
            U32 => NumUnsigned(u32::arbitrary(g) as u64, *ty),
            U64 => NumUnsigned(u64::arbitrary(g) as u64, *ty),
        },
        Type::Signed(ty) => match ty {
            I8 => NumSigned(i8::arbitrary(g) as i64, *ty),
            I16 => NumSigned(i16::arbitrary(g) as i64, *ty),
            I32 => NumSigned(i32::arbitrary(g) as i64, *ty),
            I64 => NumSigned(i64::arbitrary(g) as i64, *ty),
        },
        _ => unreachable!("only num types are supported"),
    }
}

fn apply_operator(op: &Op, x: &Literal, y: &Literal) -> Option<Literal> {
    match (x, y) {
        (NumUnsigned(x, U8), NumUnsigned(y, U8)) => apply!(op, x: u8, y: u8),
        (NumUnsigned(x, U16), NumUnsigned(y, U16)) => apply!(op, x: u16, y: u16),
        (NumUnsigned(x, U32), NumUnsigned(y, U32)) => apply!(op, x: u32, y: u32),
        (NumUnsigned(x, U64), NumUnsigned(y, U64)) => apply!(op, x: u64, y: u64),
        (NumSigned(x, I8), NumSigned(y, I8)) => apply!(op, x: i8, y: i8),
        (NumSigned(x, I16), NumSigned(y, I16)) => apply!(op, x: i16, y: i16),
        (NumSigned(x, I32), NumSigned(y, I32)) => apply!(op, x: i32, y: i32),
        (NumSigned(x, I64), NumSigned(y, I64)) => apply!(op, x: i64, y: i64),
        (x, y) => unreachable!("Incompatible x and y: {x}, {y}"),
    }
}

#[macro_export]
macro_rules! apply {
    (
        $op:ident, $x:ident:$x_ty:ty, $y:ident:$y_ty:ty
    ) => {{
        let $x = *$x as $x_ty;
        let $y = *$y as $y_ty;
        match $op {
            Add => $x.checked_add($y).map(|z| Literal::from(z)),
            Sub => $x.checked_sub($y).map(|z| Literal::from(z)),
            Mul => $x.checked_mul($y).map(|z| Literal::from(z)),
            Div => $x.checked_div($y).map(|z| Literal::from(z)),
            Mod => $x.checked_rem($y).map(|z| Literal::from(z)),
            BitAnd => Some($x & $y).map(|z| Literal::from(z)),
            BitXor => Some($x ^ $y).map(|z| Literal::from(z)),
            BitOr => Some($x | $y).map(|z| Literal::from(z)),
            GreaterThan => Some($x > $y).map(|z| Literal::from(z)),
            LessThan => Some($x < $y).map(|z| Literal::from(z)),
            Eq => Some($x == $y).map(|z| Literal::from(z)),
            NotEq => Some($x != $y).map(|z| Literal::from(z)),
            ShiftLeft => $x.checked_shl($y as u32).map(|z| Literal::from(z)),
            ShiftRight => $x.checked_shr($y as u32).map(|z| Literal::from(z)),
            ShortCircuitAnd => unreachable!("&& can only be applied to bools"),
            ShortCircuitOr => unreachable!("|| can only be applied to bools"),
        }
    }};
}

#[quickcheck]
fn quickcheck_operator(test_case: OperatorTestCase) -> Result<(), Error> {
    let OperatorTestCase { x, y, result, prg } = test_case;
    let (typed_prg, main_fn, circuit) = compile(&prg, "main")?;
    let mut eval = Evaluator::new(&typed_prg, &main_fn, &circuit);
    eval.set_literal(x)?;
    eval.set_literal(y)?;
    let output = eval.run()?;
    let output = output.into_literal();
    match output {
        Ok(output) => assert_eq!(result, Some(output)),
        Err(EvalError::Panic(_)) => assert_eq!(result, None),
        Err(e) => return Err(e.into()),
    }
    Ok(())
}
