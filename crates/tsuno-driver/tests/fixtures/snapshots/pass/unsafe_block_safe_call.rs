fn safe_callee(x: i32) -> i32
//@ req {x} == 7
//@ ens result == 8
{
    x + 1
}

fn unsafe_block_safe_call() {
    unsafe {
        let y = safe_callee(7);
        //@ assert {y} == 8;
        let _z = y;
    }
}

fn main() {}
