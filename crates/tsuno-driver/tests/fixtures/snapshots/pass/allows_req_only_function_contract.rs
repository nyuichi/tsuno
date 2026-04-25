fn req_only_contract(x: i32)
//@ req {x} == 1i32
{
    //@ assert {x} == 1i32;
}

fn main() {
    req_only_contract(1);
}
