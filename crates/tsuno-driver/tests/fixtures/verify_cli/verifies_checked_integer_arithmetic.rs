#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn arithmetic() {
    let y = 1_i32 + 1_i32;
    tsuno::assert!(y == 2);
}

fn main() {}
