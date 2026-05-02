fn unsafe_block_resource_assert_binds_where() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ let expected = 42i32;
        //@ resource assert PointsTo({p}.addr, {type i32}, Option::Some(?v)) where v == expected;
        //@ assert v == 42i32;
        //@ resource assert PointsTo({p}.addr, {type i32}, ?cell) where cell == Option::Some(42i32);
        //@ assert cell == Option::Some(42i32);
        let _keep = p;
    }
}

fn main() {}
