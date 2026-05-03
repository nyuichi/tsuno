unsafe fn keep_dealloc_token(p: *mut i32)
//@ resource req DeallocToken({p}.addr, 4usize, 4usize);
//@ resource ens DeallocToken({p}.addr, 4usize, 4usize);
{
}

unsafe fn calls_dealloc_token_contract(p: *mut i32)
//@ resource req DeallocToken({p}.addr, 4usize, 4usize);
//@ resource ens DeallocToken({p}.addr, 4usize, 4usize);
{
    keep_dealloc_token(p);
}

fn main() {}
