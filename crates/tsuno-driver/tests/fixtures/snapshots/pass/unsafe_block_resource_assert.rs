fn unsafe_block_resource_assert() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ resource assert (PointsTo({p}.addr, {type i32}, Option::Some(42i32)) * (Alloc({p}.addr, 4usize, 4usize)));
        let _keep = p;
    }
}

fn main() {}
