enum Millionaire {
    RichestIsA,
    RichestIsB,
    Tie,
}

fn main(a: A::u64, b: B::u64) -> Millionaire {
    if a > b {
        Millionaire::RichestIsA
    } else {
        if b > a {
            Millionaire::RichestIsB
        } else {
            Millionaire::Tie
        }
    }
}
