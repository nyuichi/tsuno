fn callee() -> i32 {
    1i32
}

fn rejects_call_inside_unsafe() {
    unsafe {
        let _x = callee();
    }
}

fn main() {}
