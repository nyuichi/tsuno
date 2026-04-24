fn first_bad() {
    //@ let X = 0;
    let _ = 0;
    //@ let X = 1;
    let _ = 1;
}

fn second_bad() -> i32
//@ req true
//@ ens {Y} == 0
{
    0
}

fn main() {
    first_bad();
    let _ = second_bad();
}
