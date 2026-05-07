fn rejects_stack_dealloc_token_reify() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        //@ raw assert DeallocToken({p}.addr, Layout { size: 4usize, align: 4usize });
        let _keep = p;
    }
}

fn main() {}
