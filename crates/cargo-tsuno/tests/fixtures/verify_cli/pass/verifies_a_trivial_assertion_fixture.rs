#[tsuno::verify]
fn ok(x: i32) {
    tsuno::assert!(x == x);
}

fn main() {}
