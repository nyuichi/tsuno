fn rejects_let_directive_without_semicolon(x: i32)
//@ let y = {x}
//@ req y == {x}
//@ ens true
{
}

fn main() {
    rejects_let_directive_without_semicolon(1);
}
