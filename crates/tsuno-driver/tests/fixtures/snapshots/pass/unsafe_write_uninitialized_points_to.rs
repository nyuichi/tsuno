unsafe fn init_i32(p: *mut i32)
//@ raw req *p |-> Option::<i32>::None;
//@ raw ens *p |-> Option::Some(5i32);
{
    *p = 5i32;
}

fn main() {}
