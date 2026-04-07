fn opaque(_: &mut i32) {}

#[tsuno::verify]
fn bad_scope(mut x: i32) {
    {
        let r = &mut x;
        opaque(r);
    }
}

fn main() {}
