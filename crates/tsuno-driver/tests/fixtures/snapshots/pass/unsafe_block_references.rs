fn unsafe_block_references() {
    let x = 12_i32;
    unsafe {
        let r = &x;
        //@ assert *{r} == 12;
        let _y = *r;
    }
}

fn main() {}
