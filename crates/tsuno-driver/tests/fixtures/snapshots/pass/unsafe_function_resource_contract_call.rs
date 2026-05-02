unsafe fn set_to_expected(p: *mut i32)
//@ let expected = 42i32;
//@ req {p}.prov == Option::Some(Provenance { base: {p}.addr })
//@ resource req *p |-> Option::Some(?old) * Alloc({p}.addr, 4usize, 4usize) where old == 0i32;
//@ resource ens *p |-> Option::Some(?v) * Alloc({p}.addr, 4usize, 4usize) where v == expected;
{
    *p = 42i32;
}

fn unsafe_function_resource_contract_call() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        set_to_expected(p);
        //@ resource assert *p |-> Option::Some(?v) where v == 42i32;
        //@ assert v == 42i32;
        let _keep = p;
    }
}

fn main() {}
