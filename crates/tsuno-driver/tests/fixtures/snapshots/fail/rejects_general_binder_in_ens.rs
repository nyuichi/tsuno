fn rejects_general_binder_in_ens(x: i32) -> i32
//@ req true
//@ ens ?V == result
{
    x
}

fn main() {
    rejects_general_binder_in_ens(1);
}
