fn mixed_contract_comments(x: i32) -> i32
//@ req {x} == 1i32 &&
/*@    {x} <= 1i32 */
//@ ens result == {x}
{
    x
}

fn inline_req_ens_contract(x: i32) -> i32
//@ req {x} == 2i32 ens result == {x}
{
    x
}

fn main() {
    mixed_contract_comments(1);
    inline_req_ens_contract(2);
}
