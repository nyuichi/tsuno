fn rejects_stack_dealloc_token_reify() {
    let mut x = 0i32;
    let p = &raw mut x;

    unsafe {
        //@ resource assert DeallocToken({p}.addr, 4usize, 4usize);
        let _keep = p;
    }
}

fn main() {}
