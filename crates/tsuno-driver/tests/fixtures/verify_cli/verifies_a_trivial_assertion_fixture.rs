#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[tsuno::verify]
fn ok(x: i32) {
    tsuno::assert!(x == x);
}

fn main() {}
