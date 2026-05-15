fn external_specified(x: i32) {
    let mut y = x;
    while y < 3 {
        y = y + 1;
    }
}

fn main() {
    external_specified(0);
}
