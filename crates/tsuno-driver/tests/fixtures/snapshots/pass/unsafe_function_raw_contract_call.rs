unsafe fn set_to_expected(p: *mut i32)
//@ let expected = 42i32;
//@ raw req *p |-> Option::Some(?old) where old == 0i32;
//@ raw ens *p |-> Option::Some(?v) where v == expected;
{
    *p = 42i32;
}

fn unsafe_function_raw_contract_call() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        set_to_expected(p);
        //@ raw assert *p |-> Option::Some(?v) where v == 42i32;
        //@ assert v == 42i32;
        let _keep = p;
    }
}

fn main() {}
