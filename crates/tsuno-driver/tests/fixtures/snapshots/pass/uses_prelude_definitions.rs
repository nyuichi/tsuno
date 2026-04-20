fn main() {
    let x = 7_i32;
    //@ prelude_eq_self({x});
    //@ assert prelude_id({x}) == {x};
}
