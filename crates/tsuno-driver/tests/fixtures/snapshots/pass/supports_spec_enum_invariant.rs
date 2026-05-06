/*@
enum Small {
    One(Int),
} where (self as Small::One).0 < 10;
*/

fn supports_spec_enum_invariant() {
    //@ let small = Small::One(9);
    //@ assert (small as Small::One).0 < 10;
}

fn main() {
    supports_spec_enum_invariant();
}
