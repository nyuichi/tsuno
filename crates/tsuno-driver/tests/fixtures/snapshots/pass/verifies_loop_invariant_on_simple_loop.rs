fn loop_ok() {
    let mut x = 0_i32;
    let n = 10_i32;
    while x < n
      //@ inv "0 <= {x} && {x} <= {n}"
    {
        if x >= 10 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
