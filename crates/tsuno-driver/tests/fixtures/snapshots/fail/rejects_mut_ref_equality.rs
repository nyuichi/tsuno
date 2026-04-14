fn rejects_mut_ref_equality(mut x: i32) {
    let r = &mut x;
    //@ assert {r} == {r};
}

fn main() {
    rejects_mut_ref_equality(0);
}
