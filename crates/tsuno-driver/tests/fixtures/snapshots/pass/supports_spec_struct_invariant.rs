/*@
struct Odd {
    n: Nat,
} where n % 2 == 1;
*/

fn supports_spec_struct_invariant() {
    //@ let odd = Odd { n: 3Nat };
    //@ assert odd.n % 2 == 1;
}

fn main() {
    supports_spec_struct_invariant();
}
