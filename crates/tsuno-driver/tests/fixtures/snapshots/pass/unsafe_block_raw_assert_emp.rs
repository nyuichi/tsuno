fn unsafe_block_raw_assert_emp() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ raw assert emp;
        //@ raw assert emp where true;
        //@ raw assert emp * *p |-?-> Option::Some(?v) where v == 42i32;
        //@ assert v == 42i32;
        //@ raw assert *p |-?-> Option::Some(?w) * emp where w == 42i32;
        let _keep = p;
    }
}

fn main() {}
