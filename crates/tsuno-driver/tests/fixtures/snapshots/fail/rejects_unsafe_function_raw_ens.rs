unsafe fn leaves_value_unchanged(p: *mut i32)
//@ raw req *p |-> Option::Some(0i32);
//@ raw ens *p |-> Option::Some(42i32);
{
}

fn rejects_unsafe_function_raw_ens() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        leaves_value_unchanged(p);
    }
}

fn main() {}
