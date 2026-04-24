fn let_directive_has_block_scope(x: i32) {
    {
        //@ let y = {x};
        //@ assert y == {x};
    }
    //@ assert {x} == {x};
}

fn main() {
    let_directive_has_block_scope(1);
}
