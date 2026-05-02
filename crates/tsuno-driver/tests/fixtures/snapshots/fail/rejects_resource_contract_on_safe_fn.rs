fn safe_with_resource_contract(p: *mut i32)
//@ resource req *p |-> Option::Some(0i32);
{
    let _keep = p;
}

fn main() {}
