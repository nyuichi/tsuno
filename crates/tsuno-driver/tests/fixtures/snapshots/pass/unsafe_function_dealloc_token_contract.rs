unsafe fn keep_dealloc_token(p: *mut i32)
//@ raw req DeallocToken({p}.addr, Layout { size: 4usize, align: 4usize });
//@ raw ens DeallocToken({p}.addr, Layout { size: 4usize, align: 4usize });
{
}

unsafe fn calls_dealloc_token_contract(p: *mut i32)
//@ raw req DeallocToken({p}.addr, Layout { size: 4usize, align: 4usize });
//@ raw ens DeallocToken({p}.addr, Layout { size: 4usize, align: 4usize });
{
    keep_dealloc_token(p);
}

fn main() {}
