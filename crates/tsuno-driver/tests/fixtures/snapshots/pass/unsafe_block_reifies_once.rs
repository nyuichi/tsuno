fn unsafe_block_reifies_once() {
    let mut x = 1i32;
    let mut y = 0i32;

    unsafe {
        let p = &raw mut x;
        y = 3i32;
        *p = y;
    }

    //@ assert {x} == 3i32;
    //@ assert {y} == 3i32;
}

fn main() {}
