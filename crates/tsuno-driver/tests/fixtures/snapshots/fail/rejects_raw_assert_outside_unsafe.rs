fn rejects_raw_assert_outside_unsafe() {
    //@ raw assert DeallocToken(0usize, Layout { size: 0usize, align: 1usize });
    let _x = 0i32;
}

fn main() {}
