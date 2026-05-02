fn rejects_wrong_resource_assert_value() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ resource assert PointsTo({p}.addr, {type i32}, Option::Some(0i32));
        let _keep = p;
    }
}

fn main() {}
