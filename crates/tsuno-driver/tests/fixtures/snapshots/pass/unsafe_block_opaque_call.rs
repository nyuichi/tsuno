fn callee() -> i32 {
    1i32
}

fn unsafe_block_opaque_call() {
    unsafe {
        let _x = callee();
    }
}

fn main() {}
