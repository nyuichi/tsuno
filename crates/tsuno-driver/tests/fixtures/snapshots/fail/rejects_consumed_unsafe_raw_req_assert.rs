unsafe fn overwrite_points_to(p: *mut i32)
//@ raw req *p |-> Option::Some(0i32);
//@ raw ens *p |-> Option::Some(1i32);
{
    *p = 1i32;
}

fn rejects_consumed_unsafe_raw_req_assert() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        overwrite_points_to(p);
        //@ raw assert *p |-> Option::Some(0i32);
        let _keep = p;
    }
}

fn main() {}
