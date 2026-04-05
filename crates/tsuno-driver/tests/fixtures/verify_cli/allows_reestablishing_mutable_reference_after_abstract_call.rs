#![feature(stmt_expr_attributes, proc_macro_hygiene)]

fn opaque(_: &mut i32) {}

#[tsuno::verify]
fn close_ok(mut x: i32) {
    let r = &mut x;
    opaque(r);
    *r = 1;
}

fn main() {}
