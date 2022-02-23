fn main(x: (bool, (u8, u8))) -> i32 {
    match x {
        (false, _) => 0,
        (_, (_, 0)) => 1,
        (_, (0, y)) => 2,
    }
}
