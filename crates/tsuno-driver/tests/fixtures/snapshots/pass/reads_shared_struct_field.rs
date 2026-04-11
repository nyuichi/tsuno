#[derive(Copy, Clone)]
struct Pair {
    left: i32,
    right: bool,
}

//@ verify
fn reads_shared_struct_field(pair: Pair) {
    let left = pair.left;
    let right = pair.right;
    //@ assert "{left} == {left} && {right} == {right}"
}

fn main() {}
