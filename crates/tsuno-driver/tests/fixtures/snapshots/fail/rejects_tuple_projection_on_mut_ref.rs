fn rejects_tuple_projection_on_mut_ref(mut x: i32) {
    let r = &mut x;
    //@ assert "{r}.0 == 0"
}

fn main() {
    rejects_tuple_projection_on_mut_ref(0);
}
