fn shadowed_binding_contracts(x: i32) {
    let mut x = 0_i32;
    while x < 3
      //@ inv "0 <= {x} && {x} <= 3"
    {
        x = x + 1;
    }
}

fn main() {}
