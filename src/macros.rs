//! Provides useful macros.

/// Create constants for [compile_with_constants](`crate::compile_with_constants`).
/// 
/// ## Example
/// ```
/// use garble_lang::{garble_consts, compile_with_constants};
/// let prg = "
/// const MY_CONST: u16 = PARTY_0::MY_CONST;
/// pub fn main(x: u16) -> u16 {
///     x + MY_CONST
/// }
/// ";
/// let consts = garble_consts!(
///     "PARTY_0" => { "MY_CONST" => 2u16 }
/// );
/// let compiled = compile_with_constants(prg, consts)
///     .expect("failed compilation");
/// ```
/// 
#[macro_export]
macro_rules! garble_consts {
    ($($party:expr => { $($const_name:expr => $val:expr),+}),+) => {
        ::std::collections::HashMap::from_iter([
            $((
                $party.to_string(),
                ::std::collections::HashMap::from_iter([
                    $(($const_name.to_string(), $crate::literal::Literal::from($val))),+
                ])
            )),+
        ])
    };
}
