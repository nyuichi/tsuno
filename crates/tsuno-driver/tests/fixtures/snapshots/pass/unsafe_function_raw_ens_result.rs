unsafe fn choose_ptr(p: *mut i32) -> *mut i32
//@ raw req *p |-> Option::Some(7i32);
//@ ens result.addr == {p}.addr && result.prov == {p}.prov && result.ty == {p}.ty
//@ raw ens *result |-> Option::Some(?v) where v == 7i32;
{
    p
}

fn unsafe_function_raw_ens_result() {
    let mut x = 7i32;
    let p = &raw mut x;

    unsafe {
        let q = choose_ptr(p);
        //@ raw assert *q |-> Option::Some(?v) where v == 7i32;
        let _keep = q;
    }
}

fn main() {}
