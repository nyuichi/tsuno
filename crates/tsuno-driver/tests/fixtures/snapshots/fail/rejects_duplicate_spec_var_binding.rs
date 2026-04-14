fn rejects_duplicate_spec_var_binding() {
    //@ assert ?X == 0;
    let _a = 0;
    //@ assert ?X == 1;
    let _b = 1;
}

fn main() {
    rejects_duplicate_spec_var_binding();
}
