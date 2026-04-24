fn echo(x: i32) -> i32
//@ let A = {x};
//@ req true
//@ ens result == A
{
    //@ assume false;
    x
}

fn main() {
    let y = 42;
    let z = echo(y);
    //@ assert {z} == {y};
}
