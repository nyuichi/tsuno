fn ens_only_contract() -> i32
//@ ens result == 3i32
{
    3
}

fn main() {
    let x = ens_only_contract();
    //@ assert {x} == 3i32;
}
