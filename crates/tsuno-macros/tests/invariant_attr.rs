#[test]
fn loop_macro_is_accepted() {
    use tsuno::invariant;

    let mut x = 0;
    loop {
        invariant!(x >= 0);
        x += 1;
        if x > 1 {
            break;
        }
    }
}
