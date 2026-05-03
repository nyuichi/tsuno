unsafe fn choose_ptr(p: *mut i32) -> *mut i32
//@ resource req *p |-> Option::Some(7i32);
//@ ens result.addr == {p}.addr && result.prov == {p}.prov && result.ty == {p}.ty
//@ resource ens *result |-> Option::Some(?v) where v == 7i32;
{
    p
}

fn unsafe_function_resource_ens_result() {
    let mut x = 7i32;
    let p = &raw mut x;

    unsafe {
        let q = choose_ptr(p);
        //@ resource assert *q |-> Option::Some(?v) where v == 7i32;
        let _keep = q;
    }
}

fn main() {}
