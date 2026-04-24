fn let_directives_bind_contract_and_body(x: i32) -> i32
//@ let y = {x};
//@ let z = y;
//@ req z == {x}
//@ ens result == z
{
    //@ let body = {x};
    //@ assert body == z;
    x
}

fn main() {
    let_directives_bind_contract_and_body(1);
}
