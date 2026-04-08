//@ verify
fn bad_loop(mut x: i32) {
    while x < 3 {
        x = x + 1;
        //@ inv "{x} <= 3"
        break;
    }
}

fn main() {}
