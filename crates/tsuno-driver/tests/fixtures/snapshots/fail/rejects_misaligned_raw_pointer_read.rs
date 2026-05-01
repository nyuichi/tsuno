fn rejects_misaligned_raw_pointer_read() {
    let p = 1usize as *const i32;

    unsafe {
        let _x = *p;
    }
}

fn main() {}
