fn rejects_directive_inside_unsafe() {
    let x = 1i32;
    let p = &raw const x;

    unsafe {
        let y = *p;
        //@ assert {y} == 1i32;
    }
}

fn main() {}
