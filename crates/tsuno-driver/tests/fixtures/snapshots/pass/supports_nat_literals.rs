fn supports_nat_literals() {
    //@ assert nat_to_i32(3Nat) == 3i32;
    //@ assert nat_to_i32(4) == 4i32;
}

fn main() {
    supports_nat_literals();
}
