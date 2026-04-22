fn main() {
    let mut x = 0_i32;
    let n = 3_i32;
    while x < n
      //@ inv 0i32 <= x && x <= {n}
    {
        x += 1;
    }
}
