fn rejects_body_spec_var_in_ens(x: i32) -> i32
//@ req "?X == x"
//@ ens "result == X + Y"
{
    //@ assert "X == x"
    let pair = (x, 1);
    //@ assert "?Y == {pair}.1"
    let out = x + 1;
    out
}

fn main() {
    let _ = rejects_body_spec_var_in_ens(3);
}
