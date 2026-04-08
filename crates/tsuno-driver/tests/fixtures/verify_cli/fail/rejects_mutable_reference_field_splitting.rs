//@ verify
fn rejects_mutable_reference_field_splitting(r: &mut (i32, bool)) {
    let left = &mut (*r).0;
    let right = &mut (*r).1;
    *left += 1;
    *right = !*right;
}

fn main() {}
