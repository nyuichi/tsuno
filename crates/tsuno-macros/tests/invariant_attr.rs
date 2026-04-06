#[test]
fn loop_macro_is_accepted() {
    let mut x = 0;
    let limit = 1;
    while x < limit {
        tsuno::inv!("0 <= {x} && {x} <= {limit}");
        x += 1;
    }
}
