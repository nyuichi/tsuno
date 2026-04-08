//@ verify
fn prophecy_everywhere(x: i32) {
    //@ assert "{^:x} == {^:x}"
    let mut y = x;
    while y < 1
      //@ inv "{^:x} == {^:x}"
    {
        break;
    }

    let _sink = y;
}

//@ req "{^:x} == {^:x}"
//@ ens "{^:x} == {^:x}"
fn id(x: i32) -> i32 {
    x
}

fn main() {}
