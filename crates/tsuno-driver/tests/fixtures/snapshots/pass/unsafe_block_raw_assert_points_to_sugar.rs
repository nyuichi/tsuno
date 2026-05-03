fn unsafe_block_raw_assert_points_to_sugar() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ raw assert *p |-> Option::Some(?v) where v == 42i32;
        //@ assert v == 42i32;
        //@ raw assert *p |-> Option::Some(42i32);
        let _keep = p;
    }
}

fn main() {}
