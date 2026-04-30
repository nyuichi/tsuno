fn rejects_null_raw_pointer_read() {
    let p = 0usize as *const i32;

    unsafe {
        let _x = *p;
    }
}

fn main() {}
