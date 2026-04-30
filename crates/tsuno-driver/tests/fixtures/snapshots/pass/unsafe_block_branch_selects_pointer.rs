fn unsafe_block_branch_selects_pointer(flag: bool) {
    let mut x = 0i32;
    let mut y = 0i32;
    let mut z = 42i32;

    unsafe {
        let p = if flag { &raw mut x } else { &raw mut y };
        z = *p;
        *p = 1i32;
    }

    //@ assert {z} == 0i32;
    //@ assert 0i32 <= {x} && {x} <= 1i32;
    //@ assert 0i32 <= {y} && {y} <= 1i32;
    //@ assert {x} + {y} == 1i32;
}

fn main() {}
