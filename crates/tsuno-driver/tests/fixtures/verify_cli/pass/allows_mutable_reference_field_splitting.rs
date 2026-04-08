//@ verify
fn allows_mutable_reference_field_splitting(r: &mut (i32, bool)) {
    let left = &mut (*r).0;
    let right = &mut (*r).1;
    *left = 2;
    *right = !*right;
}

//@ verify
fn allows_mutable_reference_field_splitting_three(r: &mut (i32, bool, i32)) {
    let left = &mut (*r).0;
    let middle = &mut (*r).1;
    let right = &mut (*r).2;
    *left = 2;
    *middle = !*middle;
    *right = 3;
}

fn main() {}
