//@ req "true"
//@ ens "{x}.fin == 2"
fn set_to_two(x: &mut i32) {
    *x = 3;
}

fn main() {}
