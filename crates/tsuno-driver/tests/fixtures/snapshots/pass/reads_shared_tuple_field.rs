//@ verify
fn reads_shared_tuple_field(p: &(i32, bool)) {
    let a = (*p).0;
    let b = (*p).1;
    //@ assert "{a} == {a} && {b} == {b}"
}

fn main() {}
