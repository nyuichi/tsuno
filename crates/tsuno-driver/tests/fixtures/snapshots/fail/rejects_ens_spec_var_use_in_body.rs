//@ verify
//@ req "true"
//@ ens "?X == result"
fn rejects_ens_spec_var_use_in_body() -> i32 {
    //@ assert "X == 0"
    let out = 0;
    out
}

fn main() {
    let _ = rejects_ens_spec_var_use_in_body();
}
