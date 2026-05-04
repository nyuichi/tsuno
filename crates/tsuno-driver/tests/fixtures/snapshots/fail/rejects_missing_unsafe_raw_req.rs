unsafe fn needs_points_to(p: *mut i32)
//@ raw req *p |-> Option::Some(1i32);
//@ raw ens *p |-> Option::Some(1i32);
{
}

fn rejects_missing_unsafe_raw_req() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        needs_points_to(p);
    }
}

fn main() {}
