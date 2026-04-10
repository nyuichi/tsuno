//@ verify
//@ req "?X == x"
//@ ens "result == X + Y"
fn verifies_spec_vars_across_function_directives(x: i32) -> i32 {
    //@ assert "X == x"
    let pair = (x, 1);
    //@ assert "?Y == {pair}.1"
    let out = x + 1;
    out
}

fn main() {
    let _ = verifies_spec_vars_across_function_directives(3);
}
