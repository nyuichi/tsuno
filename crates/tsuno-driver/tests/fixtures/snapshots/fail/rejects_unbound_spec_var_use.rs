fn rejects_unbound_spec_var_use() {
    //@ assert X == 0;
    let _ = ();
}

fn main() {
    rejects_unbound_spec_var_use();
}
