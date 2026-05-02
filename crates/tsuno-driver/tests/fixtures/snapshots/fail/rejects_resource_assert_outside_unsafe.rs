fn rejects_resource_assert_outside_unsafe() {
    //@ resource assert Alloc(0usize, 0usize, 1usize);
    let _x = 0i32;
}

fn main() {}
