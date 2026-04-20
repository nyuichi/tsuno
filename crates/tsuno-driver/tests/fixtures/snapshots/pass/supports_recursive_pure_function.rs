/*@
fn len(xs: List<i32>) -> i32 {
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
    }
}
*/

fn main() {
    //@ assert len(List::Cons(0i32, List::Nil)) == 1i32;
}
