fn rejects_raw_pointer_write_missing_points_to() {
    let p = 4usize as *mut i32;

    unsafe {
        *p = 1i32;
    }
}

fn main() {}
