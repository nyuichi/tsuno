fn unsafe_block_checked_arithmetic() {
    unsafe {
        let x = 40_i32;
        let y = x + 2;
        //@ assert {y} == 42;
        let _z = y;
    }
}

fn main() {}
