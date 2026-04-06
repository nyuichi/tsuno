use tsuno::invariant;

#[tsuno::verify]
fn bad_loop(mut x: i32) {
    loop {
        invariant!(x <= 1);
        if x == 0 {
            x = 1;
            continue;
        }
        if x == 1 {
            x = 2;
            continue;
        }
        break;
    }
}

fn main() {}
