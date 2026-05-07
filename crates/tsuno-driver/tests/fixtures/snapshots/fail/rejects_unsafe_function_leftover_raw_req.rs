unsafe fn leaves_dealloc_token(p: *mut i32)
//@ raw req DeallocToken({p}.addr, Layout { size: 4usize, align: 4usize });
{
}

fn main() {}
