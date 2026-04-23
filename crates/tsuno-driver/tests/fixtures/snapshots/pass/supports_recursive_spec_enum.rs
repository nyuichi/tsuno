/*@
enum IntList {
    Nil,
    Cons(i32, IntList),
}

fn singleton(x: i32) -> IntList {
    IntList::Cons(x, IntList::Nil)
}
*/

fn builds_recursive_spec_enum(x: i32) {
    //@ assert singleton({x}) == IntList::Cons({x}, IntList::Nil);
}

fn main() {}
