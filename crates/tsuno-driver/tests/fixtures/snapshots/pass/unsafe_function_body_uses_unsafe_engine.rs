unsafe fn write_through_raw_pointer() {
    let mut x = 0i32;
    let p = &raw mut x;
    *p = 1i32;
    let _keep = p;
}

fn unsafe_function_body_uses_unsafe_engine() {
    unsafe {
        write_through_raw_pointer();
    }
}

fn main() {}
