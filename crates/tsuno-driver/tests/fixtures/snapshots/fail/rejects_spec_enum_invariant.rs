/*@
enum Small {
    One(Int),
} where (self as Small::One).0 < 10;
*/

fn rejects_spec_enum_invariant() {
    //@ let small = Small::One(10);
    //@ assert (small as Small::One).0 == 10;
}

fn main() {
    rejects_spec_enum_invariant();
}
