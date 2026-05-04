fn rejects_legacy_resource_assert_keyword() {
    let mut x = 0i32;
    let p = &raw mut x;
    unsafe {
        //@ resource assert *p |-> Option::Some(0i32);
        let _keep = p;
    }
}

fn main() {}
