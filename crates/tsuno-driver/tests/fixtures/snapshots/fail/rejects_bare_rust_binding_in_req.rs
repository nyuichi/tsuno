fn id(x: i32) -> i32
//@ req x == 1i32
//@ ens {result} == {x}
{
    x
}

fn main() {
    let _ = id(1);
}
