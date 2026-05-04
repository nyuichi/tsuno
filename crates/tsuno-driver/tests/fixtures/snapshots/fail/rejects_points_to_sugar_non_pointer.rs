fn rejects_points_to_sugar_non_pointer() {
    let x = 42i32;

    unsafe {
        //@ raw assert *x |-> Option::Some(42i32);
        let _keep = x;
    }
}

fn main() {}
