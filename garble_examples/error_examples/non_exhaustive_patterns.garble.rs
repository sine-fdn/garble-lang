pub fn main(x: (bool, (u8, u8))) -> i32 {
    match x {
        (false, _) => 0u8,
        (_, (_, 0u8)) => 1u8,
        (_, (0u8, y)) => 2u8,
    }
}
