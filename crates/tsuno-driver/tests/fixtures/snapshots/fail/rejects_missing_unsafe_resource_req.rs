unsafe fn needs_points_to(p: *mut i32)
//@ resource req *p |-> Option::Some(1i32);
//@ resource ens *p |-> Option::Some(1i32);
{
}

fn rejects_missing_unsafe_resource_req() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        needs_points_to(p);
    }
}

fn main() {}
