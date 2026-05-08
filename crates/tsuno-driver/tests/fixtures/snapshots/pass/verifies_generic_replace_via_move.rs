#![feature(core_intrinsics)]
#![allow(internal_features)]

struct Pair {
    a: i32,
    b: i32,
}

unsafe fn replace<T>(dst: *mut T, src: T) -> T
//@ let replacement = {src};
//@ raw req *dst |-> Option::Some(?old);
//@ raw ens *dst |-> Option::Some(?new) where new == replacement;
//@ ens result == old
{
    unsafe {
        let old = core::intrinsics::read_via_copy::<T>(dst as *const T);
        core::intrinsics::write_via_move::<T>(dst, src);
        old
    }
}

unsafe fn caller_i32(p: *mut i32, src: i32) -> i32
//@ let replacement = {src};
//@ raw req *p |-> Option::Some(?old);
//@ raw ens *p |-> Option::Some(?new) where new == replacement;
//@ ens result == old
{
    unsafe { replace::<i32>(p, src) }
}

unsafe fn caller_pair(p: *mut Pair, src: Pair) -> Pair
//@ let replacement = {src};
//@ raw req *p |-> Option::Some(?old);
//@ raw ens *p |-> Option::Some(?new) where new == replacement;
//@ ens result == old
{
    unsafe { replace::<Pair>(p, src) }
}

fn main() {}
