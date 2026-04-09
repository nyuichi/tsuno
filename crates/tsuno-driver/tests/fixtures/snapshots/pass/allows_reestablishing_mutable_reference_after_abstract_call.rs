fn opaque(_: &mut i32) {}

//@ verify
fn close_ok(mut x: i32) {
    let r = &mut x;
    opaque(r);
    *r = 1;
}

fn main() {}
