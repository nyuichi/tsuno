#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn loop_ok() {
    let mut x = 0_i32;
    #[tsuno::invariant(x <= 10)]
    loop {
        if x >= 10 {
            break;
        }
        x = x + 1;
    }
}

fn main() {}
