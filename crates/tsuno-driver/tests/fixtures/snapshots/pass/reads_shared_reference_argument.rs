//@ verify
fn reads_shared_reference_argument(x: &i32) {
    let y = *x;
    //@ assert "{y} == {x}"
}

fn main() {}
