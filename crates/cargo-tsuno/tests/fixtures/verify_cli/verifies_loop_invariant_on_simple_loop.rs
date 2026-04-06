#![feature(stmt_expr_attributes, proc_macro_hygiene)]

use tsuno::invariant;

#[tsuno::verify]
fn loop_ok() {
    let mut x = 0_i32;
    loop {
        invariant!(x <= 10);
        if x >= 10 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
