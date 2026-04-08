//@ verify
fn partial_move_then_remaining_field_write() {
    let mut pair = (1_i32, false);
    let _taken = pair.0;
    pair.1 = true;
    let y = pair.1;
    //@ assert "{y} == true"
}

//@ verify
fn partial_move_then_remaining_field_write_three() {
    let mut value = 1_i32;
    let mut triple = (&mut value, false, false);
    let _taken = triple.0;
    triple.1 = true;
    triple.2 = true;
    let y = triple.1;
    let _z = triple.2;
    //@ assert "{y} == true"
}

fn main() {}
