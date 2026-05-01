fn unsafe_block_branch(flag: bool) {
    let mut x = 1i32;

    unsafe {
        let p = &raw mut x;
        if flag {
            *p = 2i32;
        } else {
            *p = 3i32;
        }
    }

    //@ assert 2i32 <= {x} && {x} <= 3i32;
}

fn main() {}
