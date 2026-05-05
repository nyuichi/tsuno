unsafe fn empty_raw_contract()
//@ raw req emp;
//@ raw ens emp;
{
}

unsafe fn preserves_i32_with_emp(p: *mut i32)
//@ raw req emp * *p |-> Option::Some(?old) where old == 42i32;
//@ raw ens *p |-> Option::Some(?v) * emp where v == old;
{
}

fn unsafe_function_raw_contract_emp() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        empty_raw_contract();
        preserves_i32_with_emp(p);
        //@ raw assert *p |-> Option::Some(?v) where v == 42i32;
        //@ assert v == 42i32;
        let _keep = p;
    }
}

fn main() {}
