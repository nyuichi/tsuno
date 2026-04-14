struct Droppy {
    value: i32,
}

impl Drop for Droppy {
    fn drop(&mut self) {}
}

fn rejects_drop_struct_initial_state(value: Droppy) {
    //@ assert true;
}

fn main() {}
