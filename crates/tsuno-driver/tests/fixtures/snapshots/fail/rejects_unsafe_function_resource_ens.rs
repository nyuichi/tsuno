unsafe fn leaves_value_unchanged(p: *mut i32)
//@ resource req *p |-> Option::Some(0i32);
//@ resource ens *p |-> Option::Some(42i32);
{
}

fn rejects_unsafe_function_resource_ens() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        leaves_value_unchanged(p);
    }
}

fn main() {}
