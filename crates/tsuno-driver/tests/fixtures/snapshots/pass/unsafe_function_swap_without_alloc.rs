unsafe fn swap_i32(p: *mut i32, q: *mut i32)
//@ req {p}.addr != {q}.addr
//@ raw req *p |-> Option::Some(?old_p) * *q |-> Option::Some(?old_q);
//@ raw ens *p |-> Option::Some(?new_p) * *q |-> Option::Some(?new_q) where new_p == old_q && new_q == old_p;
{
    let tmp = *p;
    *p = *q;
    *q = tmp;
}

fn unsafe_function_swap_without_alloc() {
    let mut x = 1i32;
    let mut y = 2i32;
    let p = &raw mut x;
    let q = &raw mut y;

    unsafe {
        swap_i32(p, q);
        //@ assert {x} == 2i32;
        //@ assert {y} == 1i32;
    }
}

fn main() {}
