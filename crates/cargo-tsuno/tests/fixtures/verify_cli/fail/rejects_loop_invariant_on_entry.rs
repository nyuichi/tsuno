#[tsuno::verify]
fn bad_loop(mut x: i32) {
    if x > 1 {
        x = 1;
    }
    while x < 3
      //@ inv "x <= 1"
    {
        x = 2;
        continue;
        break;
    }
}

fn main() {}
