fn main() {
    //@ nat_add_zero_right(Nat::Succ(Nat::Succ(Nat::Zero)));
    //@ nat_add_assoc(Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero), Nat::Succ(Nat::Zero));
    //@ list_append_nil_right(List::<i32>::Cons(0i32, List::<i32>::Nil));
    //@ list_append_assoc(List::<i32>::Cons(0i32, List::<i32>::Nil), List::<i32>::Cons(1i32, List::<i32>::Nil), List::<i32>::Cons(2i32, List::<i32>::Nil));
    //@ list_len_append(List::<i32>::Cons(0i32, List::<i32>::Nil), List::<i32>::Cons(1i32, List::<i32>::Cons(2i32, List::<i32>::Nil)));
    //@ assert nat_to_i32(Nat::Succ(Nat::Succ(Nat::Succ(Nat::Zero)))) == 3i32;
    //@ assert seq_rev::<i32>([0i32, 1i32]) == [1i32, 0i32];
    //@ seq_rev_empty::<i32>([]);
}
