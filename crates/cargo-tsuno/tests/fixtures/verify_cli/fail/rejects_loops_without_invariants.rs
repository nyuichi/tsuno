#[tsuno::verify]
fn bad_loop(mut x: i32) {
    loop {
        if x > 0 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
