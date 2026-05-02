fn unsafe_block_resource_assert_points_to_sugar_single_tuple() {
    let mut x = (42i32,);
    let p = &raw mut x;

    unsafe {
        //@ resource assert *p |-> Option::Some(?v) where v.0 == 42i32;
        let _keep = p;
    }
}

fn main() {}
