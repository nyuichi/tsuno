fn bump(x: &mut i32) -> i32 {
    *x += 1;
    *x
}

fn bad_after_call(mut x: i32) {
    let r = &mut x;
    let _ = bump(r);
    //@ assert "{x} == 0"
}

fn main() {}
