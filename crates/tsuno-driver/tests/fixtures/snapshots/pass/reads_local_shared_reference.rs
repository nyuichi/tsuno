//@ verify
fn reads_local_shared_reference(x: i32) {
    let r = &x;
    let y = *r;
    //@ assert "{y} == {x}"
}

fn main() {}
