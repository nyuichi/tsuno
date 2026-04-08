//@ verify
fn partial_move_then_remaining_field_write() {
    let mut pair = (1_i32, false);
    let _taken = pair.0;
    pair.1 = true;
    let y = pair.1;
    //@ assert "y == true"
}

fn main() {}
