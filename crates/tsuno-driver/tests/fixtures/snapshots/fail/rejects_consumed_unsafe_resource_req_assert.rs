unsafe fn consume_points_to(p: *mut i32)
//@ resource req *p |-> Option::Some(0i32);
{
}

fn rejects_consumed_unsafe_resource_req_assert() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        consume_points_to(p);
        //@ resource assert *p |-> Option::Some(0i32);
        let _keep = p;
    }
}

fn main() {}
