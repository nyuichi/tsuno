//@ verify
fn bad_loop(mut x: i32) {
    while x < 3 {
        if x > 0 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
