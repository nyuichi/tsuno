struct NoCopy {
    value: i32,
}

fn rejects_moved_raw_pointer_read() {
    let x = NoCopy { value: 7i32 };
    let p = &raw const x.value;
    let _moved = x;

    unsafe {
        let _y = *p;
    }
}

fn main() {}
