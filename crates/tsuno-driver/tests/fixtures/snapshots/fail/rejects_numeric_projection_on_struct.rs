#[derive(Copy, Clone)]
struct Pair {
    left: i32,
    right: bool,
}

fn rejects_numeric_projection_on_struct(pair: Pair) {
    //@ assert {pair}.0 == 0i32;
}

fn main() {
    let pair = Pair {
        left: 0,
        right: false,
    };
    let _ = pair.right;
    rejects_numeric_projection_on_struct(pair);
}
