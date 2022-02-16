enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
}

enum OpResult {
    Ok(u8),
    DivByZero,
}

fn main(values: (u8, u8), op: Op) -> OpResult {
    match (op, values) {
        (Op::Add, (x, y)) => OpResult::Ok(x + y),
        (Op::Sub, (x, y)) => OpResult::Ok(x - y),
        (Op::Mul, (x, y)) => OpResult::Ok(x * y),
        (Op::Min, (x, y)) => OpResult::Ok(if x < y { x } else { y }),
        (Op::Max, (x, y)) => OpResult::Ok(if x > y { x } else { y }),
        (Op::Div, (x, 0)) => OpResult::DivByZero,
        (Op::Div, (x, y)) => OpResult::Ok(x / y),
    }
}
