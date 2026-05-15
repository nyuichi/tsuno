fn rejects_unknown_spec_struct_literal() {
    //@ assert Unknown { x: 1i32 }.x == 1i32;
}

fn main() {
    rejects_unknown_spec_struct_literal();
}
