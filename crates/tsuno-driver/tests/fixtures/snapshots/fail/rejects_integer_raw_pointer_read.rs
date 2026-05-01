fn rejects_integer_raw_pointer_read() {
    let p = 4usize as *const i32;

    unsafe {
        let _x = *p;
    }
}

fn main() {}
