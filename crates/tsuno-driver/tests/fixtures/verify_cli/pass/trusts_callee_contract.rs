//@ verify
fn caller() {
    let y = callee();
    let z = y + 1;
    //@ assert "z == 4"
    let _sink = z;
}

//@ req "true"
//@ ens "{result} == 3"
fn callee() -> i32 {
    2
}

fn main() {}
