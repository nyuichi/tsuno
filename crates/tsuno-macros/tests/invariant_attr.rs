#![feature(stmt_expr_attributes, proc_macro_hygiene)]

#[test]
fn loop_attribute_is_accepted() {
    let mut x = 0;
    #[tsuno::invariant(x >= 0)]
    loop {
        x += 1;
        if x > 1 {
            break;
        }
    }
}
