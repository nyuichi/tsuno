fn allows_mutable_reference_to_tuple_initial_state(x: &mut (i32, bool)) {
    //@ assert "true"
}

fn allows_mutable_reference_to_tuple_initial_state_three(x: &mut (i32, bool, i32)) {
    //@ assert "true"
}

fn main() {}
