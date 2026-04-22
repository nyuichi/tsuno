fn id(x: i32) -> i32
//@ req true
//@ ens ?result == {x}
{
    x
}

fn main() {
    let _ = id(1);
}
