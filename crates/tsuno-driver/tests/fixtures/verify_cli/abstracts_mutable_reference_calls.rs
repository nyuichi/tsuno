#![feature(stmt_expr_attributes, proc_macro_hygiene)]

fn bump(x: &mut i32) -> i32 {
    *x += 1;
    *x
}

#[tsuno::verify]
fn bad_after_call(mut x: i32) {
    let r = &mut x;
    let _ = bump(r);
    tsuno::assert!(x == 0);
}

fn main() {}
