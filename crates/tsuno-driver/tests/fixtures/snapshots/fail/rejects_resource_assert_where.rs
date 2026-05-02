fn rejects_resource_assert_where() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ resource assert PointsTo({p}.addr, {type i32}, Option::Some(?v)) where v > 50i32;
        let _keep = p;
    }
}

fn main() {}
