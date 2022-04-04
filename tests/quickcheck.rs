#![cfg(feature = "fuzz")]

use garble::{
    compile,
    eval::{EvalError, Evaluator},
    Error,
};
use quickcheck_macros::quickcheck;

#[macro_export]
macro_rules! quickcheck_for {
    (
        [$( $fn_name:ident($x: ident: $x_ty: ty, $y:ident: $y_ty: ty) -> $z_ty: ty), *],
        $prg_ident:ident = $prg:literal,
        $test_fn:block
    ) => {
        $(
            #[quickcheck]
            fn $fn_name($x: $x_ty, $y: $y_ty) -> Result<bool, Error> {
                type RetTy = $z_ty;
                let $prg_ident = format!($prg, stringify!($x_ty), stringify!($y_ty), stringify!($z_ty));
                let (typed_prg, main_fn, circuit) = compile(&$prg_ident, "main")?;
                let mut $prg_ident = Evaluator::new(&typed_prg, &main_fn, &circuit);
                $prg_ident.parse_literal(&format!("{}{}", $x, stringify!($x_ty)))?;
                $prg_ident.parse_literal(&format!("{}{}", $y, stringify!($y_ty)))?;
                $test_fn
            }
        )*
    };
}

quickcheck_for! {
    [
        compile_add_u8(x: u8, y: u8) -> u8,
        compile_add_u16(x: u16, y: u16) -> u16,
        compile_add_u32(x: u32, y: u32) -> u32,
        compile_add_u64(x: u64, y: u64) -> u64,
        compile_add_u128(x: u128, y: u128) -> u128,
        compile_add_i8(x: i8, y: i8) -> i8,
        compile_add_i16(x: i16, y: i16) -> i16,
        compile_add_i32(x: i32, y: i32) -> i32,
        compile_add_i64(x: i64, y: i64) -> i64,
        compile_add_i128(x: i128, y: i128) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x + y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x + y),
            Err(EvalError::Panic(_)) => Ok(x.checked_add(y).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_sub_u8(x: u8, y: u8) -> u8,
        compile_sub_u16(x: u16, y: u16) -> u16,
        compile_sub_u32(x: u32, y: u32) -> u32,
        compile_sub_u64(x: u64, y: u64) -> u64,
        compile_sub_u128(x: u128, y: u128) -> u128,
        compile_sub_i8(x: i8, y: i8) -> i8,
        compile_sub_i16(x: i16, y: i16) -> i16,
        compile_sub_i32(x: i32, y: i32) -> i32,
        compile_sub_i64(x: i64, y: i64) -> i64,
        compile_sub_i128(x: i128, y: i128) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x - y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x - y),
            Err(EvalError::Panic(_)) => Ok(x.checked_sub(y).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_mul_u8(x: u8, y: u8) -> u8,
        compile_mul_u16(x: u16, y: u16) -> u16,
        compile_mul_u32(x: u32, y: u32) -> u32,
        compile_mul_u64(x: u64, y: u64) -> u64,
        compile_mul_u128(x: u128, y: u128) -> u128,
        compile_mul_i8(x: i8, y: i8) -> i8,
        compile_mul_i16(x: i16, y: i16) -> i16,
        compile_mul_i32(x: i32, y: i32) -> i32,
        compile_mul_i64(x: i64, y: i64) -> i64,
        compile_mul_i128(x: i128, y: i128) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x * y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x * y),
            Err(EvalError::Panic(_)) => Ok(x.checked_mul(y).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_div_u8(x: u8, y: u8) -> u8,
        compile_div_u16(x: u16, y: u16) -> u16,
        compile_div_u32(x: u32, y: u32) -> u32,
        compile_div_u64(x: u64, y: u64) -> u64,
        compile_div_u128(x: u128, y: u128) -> u128,
        compile_div_i8(x: i8, y: i8) -> i8,
        compile_div_i16(x: i16, y: i16) -> i16,
        compile_div_i32(x: i32, y: i32) -> i32,
        compile_div_i64(x: i64, y: i64) -> i64,
        compile_div_i128(x: i128, y: i128) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x / y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x / y),
            Err(EvalError::Panic(_)) => Ok(x.checked_div(y).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_mod_u8(x: u8, y: u8) -> u8,
        compile_mod_u16(x: u16, y: u16) -> u16,
        compile_mod_u32(x: u32, y: u32) -> u32,
        compile_mod_u64(x: u64, y: u64) -> u64,
        compile_mod_u128(x: u128, y: u128) -> u128,
        compile_mod_i8(x: i8, y: i8) -> i8,
        compile_mod_i16(x: i16, y: i16) -> i16,
        compile_mod_i32(x: i32, y: i32) -> i32,
        compile_mod_i64(x: i64, y: i64) -> i64,
        compile_mod_i128(x: i128, y: i128) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x % y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x % y),
            Err(EvalError::Panic(_)) => Ok(x.checked_rem(y).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_shl_u8(x: u8, y: u8) -> u8,
        compile_shl_u16(x: u16, y: u8) -> u16,
        compile_shl_u32(x: u32, y: u8) -> u32,
        compile_shl_u64(x: u64, y: u8) -> u64,
        compile_shl_u128(x: u128, y: u8) -> u128,
        compile_shl_i8(x: i8, y: u8) -> i8,
        compile_shl_i16(x: i16, y: u8) -> i16,
        compile_shl_i32(x: i32, y: u8) -> i32,
        compile_shl_i64(x: i64, y: u8) -> i64,
        compile_shl_i128(x: i128, y: u8) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x << y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x << y),
            Err(EvalError::Panic(_)) => Ok(x.checked_shl(y as u32).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_shr_u8(x: u8, y: u8) -> u8,
        compile_shr_u16(x: u16, y: u8) -> u16,
        compile_shr_u32(x: u32, y: u8) -> u32,
        compile_shr_u64(x: u64, y: u8) -> u64,
        compile_shr_u128(x: u128, y: u8) -> u128,
        compile_shr_i8(x: i8, y: u8) -> i8,
        compile_shr_i16(x: i16, y: u8) -> i16,
        compile_shr_i32(x: i32, y: u8) -> i32,
        compile_shr_i64(x: i64, y: u8) -> i64,
        compile_shr_i128(x: i128, y: u8) -> i128
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x >> y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == x >> y),
            Err(EvalError::Panic(_)) => Ok(x.checked_shr(y as u32).is_none()),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_lt_u8(x: u8, y: u8) -> bool,
        compile_lt_u16(x: u16, y: u16) -> bool,
        compile_lt_u32(x: u32, y: u32) -> bool,
        compile_lt_u64(x: u64, y: u64) -> bool,
        compile_lt_u128(x: u128, y: u128) -> bool,
        compile_lt_i8(x: i8, y: i8) -> bool,
        compile_lt_i16(x: i16, y: i16) -> bool,
        compile_lt_i32(x: i32, y: i32) -> bool,
        compile_lt_i64(x: i64, y: i64) -> bool,
        compile_lt_i128(x: i128, y: i128) -> bool
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x < y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == (x < y)),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_gt_u8(x: u8, y: u8) -> bool,
        compile_gt_u16(x: u16, y: u16) -> bool,
        compile_gt_u32(x: u32, y: u32) -> bool,
        compile_gt_u64(x: u64, y: u64) -> bool,
        compile_gt_u128(x: u128, y: u128) -> bool,
        compile_gt_i8(x: i8, y: i8) -> bool,
        compile_gt_i16(x: i16, y: i16) -> bool,
        compile_gt_i32(x: i32, y: i32) -> bool,
        compile_gt_i64(x: i64, y: i64) -> bool,
        compile_gt_i128(x: i128, y: i128) -> bool
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x > y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == (x > y)),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_eq_u8(x: u8, y: u8) -> bool,
        compile_eq_u16(x: u16, y: u16) -> bool,
        compile_eq_u32(x: u32, y: u32) -> bool,
        compile_eq_u64(x: u64, y: u64) -> bool,
        compile_eq_u128(x: u128, y: u128) -> bool,
        compile_eq_i8(x: i8, y: i8) -> bool,
        compile_eq_i16(x: i16, y: i16) -> bool,
        compile_eq_i32(x: i32, y: i32) -> bool,
        compile_eq_i64(x: i64, y: i64) -> bool,
        compile_eq_i128(x: i128, y: i128) -> bool
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x == y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == (x == y)),
            Err(e) => Err(e.into()),
        }
    }
}

quickcheck_for! {
    [
        compile_ne_u8(x: u8, y: u8) -> bool,
        compile_ne_u16(x: u16, y: u16) -> bool,
        compile_ne_u32(x: u32, y: u32) -> bool,
        compile_ne_u64(x: u64, y: u64) -> bool,
        compile_ne_u128(x: u128, y: u128) -> bool,
        compile_ne_i8(x: i8, y: i8) -> bool,
        compile_ne_i16(x: i16, y: i16) -> bool,
        compile_ne_i32(x: i32, y: i32) -> bool,
        compile_ne_i64(x: i64, y: i64) -> bool,
        compile_ne_i128(x: i128, y: i128) -> bool
    ],
    prg = "pub fn main(x: {}, y: {}) -> {} {{ x != y }}",
    {
        let output = prg.run()?;
        match RetTy::try_from(output) {
            Ok(output) => Ok(output == (x != y)),
            Err(e) => Err(e.into()),
        }
    }
}
