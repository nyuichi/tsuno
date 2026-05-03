unsafe fn produce_dealloc_token(p: *mut i32)
//@ resource ens DeallocToken({p}.addr, 4usize, 4usize);
{
    //@ assume false;
}

fn rejects_unsafe_block_leftover_dealloc_token() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        produce_dealloc_token(p);
        let _keep = p;
    }
}

fn main() {}
