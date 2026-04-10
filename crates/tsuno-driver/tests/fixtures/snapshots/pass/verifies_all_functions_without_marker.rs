fn helper(x: i32) -> i32 {
    x + 1
}

fn caller() {
    let y = helper(2);
    //@ assert "{y} == 3"
    let _ = y;
}

fn main() {}
