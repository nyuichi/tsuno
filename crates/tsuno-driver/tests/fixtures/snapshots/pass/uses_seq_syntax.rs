fn verifies_seq_concat() {
    //@ assert [1i32, 2i32] ++ [3i32] == [1i32, 2i32, 3i32];
}

fn verifies_seq_index_zero() {
    //@ assert ([1i32, 2i32])[Nat::Zero] == 1i32;
}

fn verifies_seq_index_succ() {
    //@ assert ([1i32, 2i32])[Nat::Succ(Nat::Zero)] == 2i32;
}

fn main() {}
