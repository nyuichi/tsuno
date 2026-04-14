fn caller() {
    let y = callee();
    let z = y + 1;
    //@ assert {z} == 4;
    let _sink = z;
}

fn callee() -> i32
//@ req true
//@ ens {result} == 3
{
    2
}

fn main() {}
