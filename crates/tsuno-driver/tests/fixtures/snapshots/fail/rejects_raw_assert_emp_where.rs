fn rejects_raw_assert_emp_where() {
    let mut x = 42i32;
    let p = &raw mut x;

    unsafe {
        //@ raw assert emp where false;
        let _keep = p;
    }
}

fn main() {}
