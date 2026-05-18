unsafe fn uses_prelude_own_i32_lemmas() {
    unsafe {
        //@ own_i32(7i32);
        //@ raw assert Own::<i32>(7i32);
        //@ drop_own_i32(7i32);
        //@ own_bool(true);
        //@ raw assert Own::<bool>(true);
        //@ drop_own_bool(true);
        //@ own_usize(3usize);
        //@ raw assert Own::<usize>(3usize);
        //@ drop_own_usize(3usize);
    }
}

fn main() {}
