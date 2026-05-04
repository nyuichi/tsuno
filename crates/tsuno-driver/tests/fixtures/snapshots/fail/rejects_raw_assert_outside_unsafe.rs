fn rejects_raw_assert_outside_unsafe() {
    //@ raw assert DeallocToken(0usize, 0usize, 1usize);
    let _x = 0i32;
}

fn main() {}
