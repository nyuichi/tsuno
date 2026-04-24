/*@
struct Foo {
    bar: isize,
    baz: bool,
}
*/

fn supports_spec_struct_literals() {
    //@ assert (Foo { bar: 42isize, baz: true }).bar == 42isize;
    //@ assert (Foo { bar: 42isize, baz: false }).baz == false;
}

fn main() {
    supports_spec_struct_literals();
}
