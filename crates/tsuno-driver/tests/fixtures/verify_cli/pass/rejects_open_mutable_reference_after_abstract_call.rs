fn opaque(_: &mut i32) {}

//@ verify
fn bad_close(mut x: i32) {
    let r = &mut x;
    opaque(r);
}

fn main() {}
