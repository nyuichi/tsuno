/*@
struct Odd {
    n: Nat,
} where n % 2 == 1;
*/

fn rejects_spec_struct_invariant() {
    //@ let odd = Odd { n: 2Nat };
    //@ assert odd.n == 2Nat;
}

fn main() {
    rejects_spec_struct_invariant();
}
