//@ verify
fn dangles_projected_move_mutable_reference() {
    let mut x = 0_i32;
    let mut y = 1_i32;
    let p = (&mut x, &mut y);
    let z = p.0;
    *z = 2;
    //@ assert "{y} == 1"
}

fn main() {}
