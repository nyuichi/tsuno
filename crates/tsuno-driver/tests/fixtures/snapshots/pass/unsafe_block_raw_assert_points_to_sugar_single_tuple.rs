fn unsafe_block_raw_assert_points_to_sugar_single_tuple() {
    let mut x = (42i32,);
    let p = &raw mut x;

    unsafe {
        //@ raw assert *p |-> Option::Some(?v) where v.0 == 42i32;
        let _keep = p;
    }
}

fn main() {}
