//@ req "true"
//@ ens "{x}.fin == 2"
fn set_to_two(x: &mut i32) {
    *x = 2;
}

fn main() {
    let mut x = 0;
    set_to_two(&mut x);
}
