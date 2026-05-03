fn safe_with_raw_contract(p: *mut i32)
//@ raw req *p |-> Option::Some(0i32);
{
    let _keep = p;
}

fn main() {}
