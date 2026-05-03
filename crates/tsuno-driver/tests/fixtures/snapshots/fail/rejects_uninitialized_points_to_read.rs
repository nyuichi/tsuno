unsafe fn read_i32(p: *mut i32)
//@ resource req *p |-> Option::<i32>::None;
{
    let _x = *p;
}

fn main() {}
