/*@
enum MyList<T> {
    Nil,
    Cons { head: T, tail: MyList<T> },
}

enum Maybe<T> {
    None,
    Some(T),
}

def singleton(x: i32) -> MyList<i32> =
    MyList::<i32>::Cons(x, MyList::<i32>::Nil)
*/

fn supports_struct_variant_selector(x: i32) {
    //@ assert (singleton({x}) as MyList::Cons).head == {x};
}

fn supports_tuple_variant_selector(x: i32) {
    //@ assert (Maybe::<i32>::Some({x}) as Maybe::Some::<i32>).0 == {x};
}

fn main() {}
