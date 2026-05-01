unsafe fn unsafe_callee() -> i32 {
    1
}

fn rejects_unsafe_fn_call_inside_unsafe() {
    unsafe {
        let _x = unsafe_callee();
    }
}

fn main() {}
