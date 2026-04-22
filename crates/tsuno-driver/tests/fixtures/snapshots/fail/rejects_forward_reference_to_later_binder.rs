fn rejects_forward_reference_to_later_binder(x: i32) {
    //@ assert V == {x} && ?V == {x};
}

fn main() {
    rejects_forward_reference_to_later_binder(1);
}
