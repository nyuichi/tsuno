#[derive(Copy, Clone)]
struct Pair {
    left: i32,
    right: bool,
}

fn reads_shared_struct_field(pair: Pair) {
    let left = pair.left;
    let right = pair.right;
    //@ assert {pair}.left == {left} && {pair}.right == {right};
}

fn main() {}
