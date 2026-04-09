fn opaque(_: &mut i32) {}

//@ verify
fn reborrow_after_opaque_move_call(mut x: i32) {
    let pair = (&mut x, ());
    opaque(pair.0);
    let y = &mut x;
    *y = 1;
}

fn main() {}
