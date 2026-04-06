#[tsuno::verify]
fn arithmetic() {
    let y = 1_i32 + 1_i32;
    tsuno::assert!(y == 2);
}

fn main() {}
