fn rejects_let_directive_out_of_scope(x: i32) {
    {
        //@ let y = {x};
        //@ assert y == {x};
    }
    //@ assert y == {x};
}

fn main() {
    rejects_let_directive_out_of_scope(1);
}
