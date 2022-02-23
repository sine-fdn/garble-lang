enum Richest {
    IsA,
    IsB,
    Tie,
}

fn main(a: u64, b: u64) -> Richest {
    if a > b {
        Richest::IsA
    } else if b > a {
        Richest::IsB
    } else {
        Richest::Tie
    }
}
