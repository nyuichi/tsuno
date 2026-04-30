fn raw_pointer_read_write() {
    let mut x = 1i32;
    let p = &raw mut x;
    let y;

    unsafe {
        y = *p;
        *p = 2i32;
    }

    //@ assert {y} == 1i32;
    //@ assert {x} == 2i32;
}

fn main() {}
