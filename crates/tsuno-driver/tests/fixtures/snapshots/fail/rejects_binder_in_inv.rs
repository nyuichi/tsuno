fn rejects_binder_in_inv(mut x: i32, n: i32) {
    while x < n
    //@ inv ?V == {x}
    {
        x = x + 1;
    }
}

fn main() {
    rejects_binder_in_inv(0, 1);
}
