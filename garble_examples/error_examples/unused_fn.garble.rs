pub fn main(x: u16) -> u16 {
    x + 1u16
}

fn inc(x: u16) -> u16 {
    add(x, 1u16)
}

fn add(x: u16, y: u16) -> u16 {
    x + y
}
