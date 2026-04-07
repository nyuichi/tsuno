#[tsuno::verify]
fn rejects_unevaluated_bool_const<const B: bool>() {
    if B {
        //@ assert "false"
    }
}

fn main() {}
