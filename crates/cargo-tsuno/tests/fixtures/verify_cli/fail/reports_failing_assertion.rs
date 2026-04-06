#[tsuno::verify]
fn bad(x: i32) {
    tsuno::assert!(x == 0);
}

fn main() {}
