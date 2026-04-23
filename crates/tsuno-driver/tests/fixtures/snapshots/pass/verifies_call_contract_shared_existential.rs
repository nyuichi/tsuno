fn echo(x: i32) -> i32
//@ req ?A == {x}
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
