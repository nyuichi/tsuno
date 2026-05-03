unsafe fn read_i32(p: *mut i32)
//@ raw req *p |-> Option::<i32>::None;
{
    let _x = *p;
}

fn main() {}
